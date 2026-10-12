"""rc4 comparison runtime shared by production and fixture runners. Apache-2.0.

This module does not select targets or establish source identity. The caller must
validate the release inventory before running, and recheck it before accepting.
"""
import os
from pathlib import Path
import re
import subprocess
import uuid

KERNELS = ('Lean default', 'nanoda', 'con-ron')
AXIOMS = frozenset(('propext', 'Classical.choice', 'Quot.sound'))
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*")


def comparison_outcome(exit_code, output):
    """Require a successful process and the four exact pinned-tool reports.

    These reports are read from a captured invocation, not supplied by a user.
    They supplement, rather than replace, source bindings and checker execution.
    """
    lines = output.splitlines()
    result = dict(
        exit_code=exit_code,
        lean_accepted='Lean default kernel accepts the solution' in lines,
        nanoda_accepted='nanoda kernel accepts the solution' in lines,
        con_ron_accepted='con-ron kernel accepts the solution' in lines,
        comparator_accepted='Your solution is okay!' in lines,
    )
    result['passed'] = exit_code == 0 and all(result[key] for key in (
        'lean_accepted', 'nanoda_accepted', 'con_ron_accepted', 'comparator_accepted'))
    return result


def require_comparison_success(outcome):
    if not outcome['passed']:
        raise ValueError(
            'Comparison acceptance failed: exit_code={exit_code}, '
            'comparator={comparator_accepted}, lean={lean_accepted}, '
            'nanoda={nanoda_accepted}, con-ron={con_ron_accepted}'.format(**outcome))


def external_config(config, bindir):
    """Add fixed checker commands to a source-bound theorem-only config.

    Never take executable overrides from a submitted configuration. Paths are
    resolved only in a runtime copy; the distributed config stays unchanged.
    """
    required = {'challenge_module', 'solution_module', 'theorem_names', 'permitted_axioms'}
    if not isinstance(config, dict) or required - config.keys() or config.keys() - (
            required | {'definition_names', 'enable_nanoda'}):
        raise ValueError('Unexpected comparison configuration keys')
    for key in ('challenge_module', 'solution_module'):
        if not isinstance(config[key], str) or not MODULE.fullmatch(config[key]):
            raise ValueError('Invalid module name: ' + key)
    if config['challenge_module'] == config['solution_module']:
        raise ValueError('Challenge and solution must be distinct')
    for key in ('theorem_names', 'definition_names', 'permitted_axioms'):
        values = config.get(key, [])
        if (not isinstance(values, list)
                or any(not isinstance(v, str) or not v for v in values)
                or len(values) != len(set(values))):
            raise ValueError('Invalid or duplicate selection: ' + key)
    if not config['theorem_names'] or not set(config['permitted_axioms']) <= AXIOMS:
        raise ValueError('Missing targets or unapproved axiom allowance')
    if config.get('definition_names'):
        raise ValueError('Definition holes are not part of this theorem-only release')
    if 'enable_nanoda' in config and config['enable_nanoda'] is not True:
        raise ValueError('Nanoda cannot be disabled')
    bindir = Path(bindir).resolve(strict=True)
    commands = {}
    for name, filename in (('nanoda', 'nanoda_bin'), ('con-ron', 'con-ron')):
        executable = bindir / filename
        if not executable.is_file() or not os.access(executable, os.X_OK):
            raise ValueError('Missing required checker: ' + filename)
        commands[name] = [str(executable)]
    result = {key: config[key] for key in required}
    result['definition_names'] = []
    result['external_kernels'] = commands
    return result


def offline_command(project, scratch, bwrap, command):
    """An offline outer sandbox; Comparator still uses its own inner sandbox."""
    project = Path(project).resolve(strict=True)
    scratch = Path(scratch).resolve(strict=True)
    bwrap = Path(bwrap).resolve(strict=True)
    if not project.is_dir() or not scratch.is_dir():
        raise ValueError('Project and scratch must be existing directories')
    if project == Path('/') or scratch == Path('/'):
        raise ValueError('Refusing a filesystem-root write binding')
    if not bwrap.is_file() or not os.access(bwrap, os.X_OK):
        raise ValueError('Missing bubblewrap executable')
    return [str(bwrap), '--ro-bind', '/', '/', '--bind', str(project), str(project),
            '--bind', str(scratch), str(scratch), '--unshare-net', '--unshare-pid',
            '--proc', '/proc', '--dev', '/dev', '--die-with-parent', '--new-session',
            '--chdir', str(project), '--', *map(str, command)]


def runtime_environment(bindir, scratch, bwrap):
    """Do not inherit Lean paths, checker overrides, or credential variables."""
    bindir, scratch, bwrap = (Path(p).resolve(strict=True) for p in (bindir, scratch, bwrap))
    return dict(PATH=str(bindir) + ':/usr/bin:/bin', HOME=str(Path.home()),
                LANG='C.UTF-8', TMPDIR=str(scratch), TMP=str(scratch), TEMP=str(scratch),
                LAKE_NO_CACHE='1', MATHLIB_NO_CACHE_ON_UPDATE='1', LEAN_ABORT_ON_PANIC='1',
                COMPARATOR_BWRAP=str(bwrap), GIT_CONFIG_NOSYSTEM='1',
                GIT_CONFIG_GLOBAL='/dev/null', GIT_TERMINAL_PROMPT='0')


def guarded(project, env, command, timeout=3600):
    """Run with the accepted VM's resource bounds and genuine offline sandbox.

    Return the captured process result; neither timeout nor partial checker output
    establishes acceptance. Stop the task-owned unit if the client wait times out.
    """
    if not isinstance(timeout, int) or isinstance(timeout, bool) or timeout <= 0:
        raise ValueError('Timeout must be a positive integer')
    if os.geteuid() == 0:
        raise ValueError('Use an unprivileged Linux user')
    unit = 'rey-check-' + uuid.uuid4().hex
    sandbox = offline_command(project, env['TMPDIR'], env['COMPARATOR_BWRAP'], command)
    forwarded = ('PATH', 'HOME', 'LANG', 'TMPDIR', 'TMP', 'TEMP', 'LAKE_NO_CACHE',
                 'MATHLIB_NO_CACHE_ON_UPDATE', 'LEAN_ABORT_ON_PANIC', 'COMPARATOR_BWRAP',
                 'GIT_CONFIG_NOSYSTEM', 'GIT_CONFIG_GLOBAL', 'GIT_TERMINAL_PROMPT')
    cmd = ['systemd-run', '--user', '--wait', '--pipe', '--collect', '--quiet', '--unit=' + unit,
           '--property=MemoryMax=6G', '--property=MemorySwapMax=0', '--property=CPUQuota=200%',
           '--property=RuntimeMaxSec=' + str(timeout), '--property=TimeoutStopSec=15',
           '--property=KillMode=control-group']
    cmd += ['--setenv=' + key + '=' + env[key] for key in forwarded]
    cmd += ['--', *sandbox]
    client_env = dict(env, XDG_RUNTIME_DIR='/run/user/' + str(os.getuid()),
                      DBUS_SESSION_BUS_ADDRESS='unix:path=/run/user/' + str(os.getuid()) + '/bus')
    try:
        return subprocess.run(cmd, env=client_env, cwd=project, capture_output=True,
                              text=True, timeout=timeout + 30)
    except subprocess.TimeoutExpired:
        subprocess.run(['systemctl', '--user', 'stop', unit], env=client_env,
                       capture_output=True, timeout=30, check=True)
        raise
