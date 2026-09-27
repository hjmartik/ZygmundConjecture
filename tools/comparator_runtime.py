"""Production and fixture runner primitives, with identical acceptance. Apache-2.0."""
import subprocess
import uuid

FORWARDED = ['PATH', 'COMPARATOR_LANDRUN', 'COMPARATOR_LEAN4EXPORT', 'COMPARATOR_NANODA',
             'TMPDIR', 'TMP', 'TEMP', 'LAKE_NO_CACHE', 'MATHLIB_NO_CACHE_ON_UPDATE']

def guarded(project, env, command, timeout=3700):
    unit = 'rey-check-' + uuid.uuid4().hex
    cmd = ['systemd-run', '--user', '--wait', '--pipe', '--collect', '--quiet', '--unit=' + unit,
           '--property=MemoryMax=6G', '--property=MemorySwapMax=0', '--property=MemoryAccounting=yes',
           '--property=CPUQuota=200%', '--property=RuntimeMaxSec=3600', '--property=TimeoutStopSec=15',
           '--property=KillMode=control-group', '--property=NoNewPrivileges=yes',
           '--property=RestrictAddressFamilies=~AF_UNIX', '--working-directory=' + str(project)]
    cmd += ['--setenv=' + key + '=' + env[key] for key in FORWARDED]
    try:
        return subprocess.run(cmd + ['--', *map(str, command)], env=env, cwd=project,
                              capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        # Stop the unit we own; a timed-out fixture/check must not leave its child
        # running in the background. This is not a retry or an acceptance result.
        subprocess.run(['systemctl', '--user', 'stop', unit], env=env, capture_output=True, timeout=30)
        raise

def comparison_outcome(exit_code, output):
    outcome = dict(exit_code=exit_code,
                   lean_accepted='Lean default kernel accepts the solution' in output,
                   nanoda_accepted='nanoda kernel accepts the solution' in output,
                   comparator_accepted='Your solution is okay!' in output)
    outcome['passed'] = exit_code == 0 and all(outcome[key] for key in
                                              ['lean_accepted', 'nanoda_accepted', 'comparator_accepted'])
    return outcome

def require_comparison_success(outcome):
    if not outcome['passed']:
        raise ValueError('Comparison acceptance failed: exit_code={exit_code}, '
                         'comparator={comparator_accepted}, lean={lean_accepted}, '
                         'nanoda={nanoda_accepted}'.format(**outcome))
