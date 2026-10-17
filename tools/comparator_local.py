#!/usr/bin/env python3
"""Local, unsandboxed comparisons for trusted project code. Apache-2.0.

This is an optional alternative, not the sandboxed Linux verification procedure.
It uses the same twenty-two specifications and requires all three proof checkers.
"""
import argparse
from datetime import datetime, timezone
import os
from pathlib import Path
import platform
import shutil
import signal
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
from common import (ROOT, LEAN, require, digest, read_json, write_json, source_manifest,
                    check_dependencies, compiler_bin, fresh_run)
from comparator import (ADAPTERS, input_hashes, validate_cases, validate_import_separation,
                        case_selection, finish_cases)
from comparator_runtime import external_config, comparison_outcome, require_comparison_success


def local_environment(bindir, scratch):
    """Keep tool selection predictable; this is not a security boundary."""
    env = {key: os.environ[key] for key in ('HOME', 'USER', 'LOGNAME', 'LANG',
           'LC_ALL', 'DEVELOPER_DIR', 'SDKROOT') if key in os.environ}
    env.update(PATH=str(bindir) + ':/usr/bin:/bin:/usr/sbin:/sbin',
               TMPDIR=str(scratch), TMP=str(scratch), TEMP=str(scratch),
               LEAN_NUM_THREADS='2', LAKE_NO_CACHE='1', MATHLIB_NO_CACHE_ON_UPDATE='1',
               LEAN_ABORT_ON_PANIC='1', GIT_CONFIG_NOSYSTEM='1',
               GIT_CONFIG_GLOBAL='/dev/null', GIT_TERMINAL_PROMPT='0')
    return env


def tool_paths(bindir):
    tools = {name: bindir / name for name in
             ('lean', 'lake', 'leanexport', 'leanchecker', 'nanoda_bin', 'con-ron')}
    for name, path in tools.items():
        require(path.is_file() and os.access(path, os.X_OK), 'Missing required executable: ' + name)
    return tools


def run_comparison(project, bindir, config, log, timeout=3600):
    """Retain full output; a timeout or interruption never establishes success."""
    require(isinstance(timeout, int) and not isinstance(timeout, bool) and timeout > 0,
            'Timeout must be a positive integer')
    scratch = project / '.lake/local-tmp'
    scratch.mkdir(parents=True, exist_ok=True)
    command = [str(bindir / 'lake'), 'comparator', '--config', str(config),
               '--inadvisably-no-sandbox']
    started = time.monotonic()
    with log.open('w') as output:
        process = subprocess.Popen(command, cwd=project, env=local_environment(bindir, scratch),
                                   stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            code = process.wait(timeout=timeout)
        except BaseException:
            # Terminate only the process group created for this invocation.
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            raise
    return dict(command=command, seconds=round(time.monotonic() - started, 3),
                log=log.name, log_sha256=digest(log),
                **comparison_outcome(code, log.read_text()))


def copy_dependencies(packages, destination):
    """Copy without modifying the original cache; use APFS clones on macOS."""
    require(not destination.exists(), 'Dependency destination already exists')
    if platform.system() == 'Darwin':
        # -c requires copy-on-write support. Do not silently make a large second
        # physical copy if the filesystem does not support it.
        subprocess.run(['/bin/cp', '-cR', str(packages), str(destination)], check=True)
    else:
        shutil.copytree(packages, destination, symlinks=True)


def run(args):
    require(args.trust_project_code,
            'This route disables Comparator\'s sandbox. Use --trust-project-code only if '
            'you trust the project code; otherwise follow verification/LINUX-SETUP.md.')
    require(platform.system() in {'Darwin', 'Linux'} and os.geteuid() != 0,
            'Use an ordinary macOS or Linux account, not root')
    manifest = source_manifest()
    cases = validate_cases()
    boundary = validate_import_separation(manifest)
    controls = {**input_hashes(), 'tools/comparator_local.py': digest(Path(__file__))}
    packages = (args.packages or LEAN / '.lake/packages').expanduser().resolve()
    dependencies = check_dependencies(packages)
    bindir = compiler_bin(args.lean_bin)
    binaries = tool_paths(bindir)
    hashes = {name: digest(path) for name, path in binaries.items()}
    require(shutil.disk_usage(ROOT).free > 15 * 1024**3, 'Need at least 15 GiB free disk')
    parent = fresh_run('comparator-local')
    report = dict(status='RUNNING', sandboxed=False, trust_project_code=True,
                  scope='Twenty-two independent results and exported dependencies; unsandboxed local checking',
                  started_utc=datetime.now(timezone.utc).isoformat(),
                  platform=platform.system(), architecture=platform.machine(),
                  cases=[], approved_cases=case_selection(cases), requested_cases=case_selection(cases),
                  completed_cases=[], controls=controls, source_files=manifest['sha256'],
                  import_separation=boundary, dependency_sources=dependencies,
                  tool_sha256=hashes, required_kernels=['Lean default', 'nanoda', 'con-ron'])
    def save():
        write_json(parent / 'report.json', report)
    save()
    print('UNSANDBOXED: this run trusts the project code not to interfere with checking.', flush=True)
    print('Run: ' + str(parent), flush=True)
    try:
        project = parent / 'project'
        project.mkdir()
        for name in manifest['sha256']:
            dest = project / name.removeprefix('lean/')
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / name, dest)
        for name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'):
            shutil.copyfile(LEAN / name, project / name)
        for path in ADAPTERS.iterdir():
            if path.name != 'CASES.json':
                shutil.copyfile(path, project / path.name)
        packet = {str(p.relative_to(project)): digest(p) for p in project.rglob('*') if p.is_file()}
        report['packet_sha256'] = packet
        save()
        (project / '.lake').mkdir()
        copy_dependencies(packages, project / '.lake/packages')
        require(check_dependencies(project / '.lake/packages') == dependencies,
                'Copied dependency sources differ')
        for case in cases:
            cfg = external_config(read_json(project / case['config']), bindir)
            config = project / ('local-' + case['config'])
            write_json(config, cfg)
            report.setdefault('runtime_configs', {})[config.name] = dict(sha256=digest(config), config=cfg)
            save()
            print('Checking ' + case['id'] + '; full log: ' + str(parent / (case['id'] + '.log')), flush=True)
            row = run_comparison(project, bindir, config, parent / (case['id'] + '.log'))
            row.update(id=case['id'], production_target=case['production_target'])
            report['cases'].append(row)
            save()
            require_comparison_success(row)
            print('PASS ' + case['id'] + ': Comparator, Lean, Nanoda and con-ron (unsandboxed)', flush=True)
        require(all(digest(project / n) == h for n, h in packet.items()), 'Packet changed during checking')
        require(all(digest(project / n) == v['sha256'] for n, v in report['runtime_configs'].items()),
                'Runtime configuration changed')
        require(source_manifest() == manifest and
                {**input_hashes(), 'tools/comparator_local.py': digest(Path(__file__))} == controls,
                'Original inputs changed')
        require(check_dependencies(packages) == dependencies and
                check_dependencies(project / '.lake/packages') == dependencies, 'Dependency sources changed')
        require({name: digest(path) for name, path in binaries.items()} == hashes, 'Checker binaries changed')
        report.update(finish_cases(cases, report['cases'], unsandboxed=True))
    except BaseException as error:
        report.update(status='FAIL', failure=repr(error))
        raise
    finally:
        report['finished_utc'] = datetime.now(timezone.utc).isoformat()
        save()
        print('Report: ' + str(parent / 'report.json'), flush=True)
    print(report['status'], flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--trust-project-code', action='store_true',
                        help='Explicitly accept execution without Comparator\'s sandbox')
    parser.add_argument('--packages', type=Path, help='Existing pinned dependency sources and local build cache')
    parser.add_argument('--lean-bin', help='Directory of the pinned local Lean executables')
    try:
        run(parser.parse_args())
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        parser.exit(1, 'Checking failed: ' + str(error) + '\n')
