#!/usr/bin/env python3
"""Seven standalone Comparator/Nanoda checks on Linux. Apache-2.0."""
import argparse
from datetime import datetime, timezone
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
from common import (ROOT, LEAN, ALLOW, require, digest, read_json, write_json,
                    source_manifest, check_dependencies, compiler_bin, fresh_run, imports)
from comparator_runtime import guarded, comparison_outcome, require_comparison_success

ADAPTERS = ROOT / 'verification/comparator'

def input_hashes():
    files = list(ADAPTERS.glob('*.lean')) + list(ADAPTERS.glob('*.json'))
    files += [ROOT / 'verification/CHECKER-PINS.json', ROOT / 'verification/AUDIT-MANIFEST.json',
              Path(__file__), ROOT / 'tools/common.py',
              ROOT / 'tools/comparator-preflight.py', ROOT / 'tools/comparator-child.py',
              ROOT / 'tools/comparator_runtime.py']
    return {str(p.relative_to(ROOT)): digest(p) for p in files}

def validate_cases():
    binding = read_json(ROOT / 'verification/AUDIT-MANIFEST.json')['sha256']
    actual = {str(p.relative_to(ROOT)) for p in ADAPTERS.iterdir() if p.suffix in {'.lean', '.json'}}
    expected = {p for p in binding if p.startswith('verification/comparator/')}
    require(len(expected) == 22 and actual == expected, 'Comparator input inventory differs')
    for name in expected:
        path = ROOT / name
        require(not path.is_symlink() and path.is_file() and digest(path) == binding[name],
                'Reviewed Comparator input differs: ' + name)
    cases = read_json(ADAPTERS / 'CASES.json')['cases']
    require(len(cases) == 7 and len({c['production_target'] for c in cases}) == 7,
            'Expected seven distinct main results')
    for i, case in enumerate(cases, 1):
        require(case['config'] == f'config-{i}.json', 'Unexpected config name')
        config = read_json(ADAPTERS / case['config'])
        require(config == dict(challenge_module=f'Challenge{i}', solution_module=f'Solution{i}',
                               theorem_names=[f'ReyMathlibOnly.target{i}'], permitted_axioms=['propext', 'Classical.choice', 'Quot.sound'],
                               enable_nanoda=True), 'Comparator configuration differs')
        solution = (ADAPTERS / f'Solution{i}.lean').read_text()
        require(case['production_target'] in solution and case['statement'] in solution,
                'Adapter mapping differs')
    return cases

def validate_import_separation(manifest):
    """Check every local import in both closures; external sources are pinned separately.

    This is a source/import boundary, not a substitute for mathematical review.
    Exact reviewed bytes are checked by source_manifest() and validate_cases().
    """
    specs = {'ReyZygmund.MathlibOnly.Definitions', 'ReyZygmund.MathlibOnly.Statements'}
    audit = read_json(ROOT / 'verification/AUDIT-MANIFEST.json')
    require(set(audit['specification_modules']) == specs, 'Specification module list differs')
    modules = {p[5:-5].replace('/', '.'): ROOT / p for p in manifest['sha256']}
    modules.update({p.stem: p for p in ADAPTERS.glob('*.lean')})
    challenges = {f'Challenge{i}' for i in range(1, 8)}
    def closure(root, statement_only):
        seen, active, external = set(), set(), set()
        def visit(name):
            require(name not in active, 'Cyclic audit import')
            if name in seen:
                return
            if name not in modules:
                require(name.split('.')[0] in {'Mathlib', 'Lean', 'Init', 'Std', 'Batteries',
                                              'Aesop', 'Qq', 'Plausible', 'ProofWidgets', 'ImportGraph', 'LeanSearchClient'},
                        'Unresolved audit import: ' + name)
                external.add(name)
                return
            if statement_only:
                require(name in specs or name == root, 'Proof-library import in Mathlib-only challenge: ' + name)
            else:
                require(name not in challenges, 'Challenge placeholder imported by solution: ' + name)
            active.add(name)
            for dependency in imports(modules[name]):
                visit(dependency)
            active.remove(name)
            seen.add(name)
        visit(root)
        if statement_only:
            require(specs <= seen, 'Incomplete independent specification closure')
        return dict(local_modules=sorted(seen), external_imports=sorted(external))
    return {f'{role}{i}': closure(f'{role}{i}', role == 'Challenge')
            for i in range(1, 8) for role in ['Challenge', 'Solution']}

def tool_paths(directory, bindir):
    pins = read_json(ROOT / 'verification/CHECKER-PINS.json')
    locations = {
        'comparator': directory / 'comparator',
        'lean4export': directory / 'comparator/.lake/packages/lean4export',
        'landrun': directory / 'landrun', 'nanoda': directory / 'nanoda'}
    bins = {'comparator': locations['comparator'] / '.lake/build/bin/comparator',
            'lean4export': locations['lean4export'] / '.lake/build/bin/lean4export',
            'landrun': locations['landrun'] / 'landrun', 'nanoda': locations['nanoda'] / 'target/release/nanoda_bin'}
    for name, repo in locations.items():
        actual = subprocess.run(['git', '-C', str(repo), 'rev-parse', 'HEAD'],
                                check=True, capture_output=True, text=True).stdout.strip()
        require(actual == pins[name]['commit'], 'Checker source pin differs: ' + name)
        dirty = subprocess.run(['git', '-C', str(repo), 'status', '--porcelain', '--untracked-files=no'],
                               check=True, capture_output=True, text=True).stdout.strip()
        require(not dirty, 'Tracked checker source changes: ' + name)
        require(bins[name].is_file() and os.access(bins[name], os.X_OK), 'Missing checker executable: ' + name)
    for name in ['lean', 'lake']:
        bins[name] = bindir / name
    return bins

def run(args):
    manifest = source_manifest()
    cases = validate_cases()
    import_separation = validate_import_separation(manifest)
    controls = input_hashes()
    parent = fresh_run('comparator')
    project = parent / 'project'
    project.mkdir()
    for name in manifest['sha256']:
        destination = project / name.removeprefix('lean/')
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / name, destination)
    for name in ['lean-toolchain', 'lake-manifest.json']:
        shutil.copyfile(LEAN / name, project / name)
    # Each adapter is an explicit Lake library; no broad default build of challenges.
    config = (LEAN / 'lakefile.toml').read_text().replace('defaultTargets = ["ReyZygmund", "Verification"]', 'defaultTargets = []')
    for i in range(1, 8):
        for role in ['Challenge', 'Solution']:
            module = role + str(i)
            shutil.copyfile(ADAPTERS / (module + '.lean'), project / (module + '.lean'))
            config += f'\n[[lean_lib]]\nname = "{module}"\n'
        shutil.copyfile(ADAPTERS / f'config-{i}.json', project / f'config-{i}.json')
    (project / 'lakefile.toml').write_text(config)
    packet_hashes = {str(p.relative_to(project)): digest(p) for p in project.rglob('*') if p.is_file()}
    report = dict(status='PREPARED_NOT_CHECKED', started_utc=datetime.now(timezone.utc).isoformat(),
                  scope='Seven main results and their exported proof closures', cases=[],
                  source_files=manifest['sha256'], packet_sha256=packet_hashes, controls=controls,
                  permitted_axioms=sorted(ALLOW), nanoda_required=True,
                  import_separation=import_separation)
    write_json(parent / 'report.json', report)
    print('Packet: ' + str(project), flush=True)
    if args.prepare_only:
        return
    require(platform.system() == 'Linux' and os.geteuid() != 0, 'Use an unprivileged Linux user')
    require(platform.machine() in ['aarch64', 'x86_64'], 'Preflight supports Linux ARM64 and x86_64')
    packages = (args.packages or LEAN / '.lake/packages').expanduser().resolve()
    checks = check_dependencies(packages)
    bindir = compiler_bin(args.lean_bin)
    bins = tool_paths(args.tools.expanduser().resolve(), bindir)
    require(shutil.disk_usage(parent).free > 15 * 1024**3, 'Need at least 15 GiB free disk')
    (project / '.lake').mkdir()
    subprocess.run(['cp', '-a', '--reflink=auto', str(packages), str(project / '.lake/packages')], check=True)
    scratch = project / '.lake/verification-tmp'
    scratch.mkdir()
    env = os.environ.copy()
    for key in ['LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT']:
        env.pop(key, None)
    env.update(PATH=str(bindir) + os.pathsep + env.get('PATH', ''),
               COMPARATOR_LANDRUN=str(bins['landrun']), COMPARATOR_LEAN4EXPORT=str(bins['lean4export']),
               COMPARATOR_NANODA=str(bins['nanoda']), TMPDIR=str(scratch), TMP=str(scratch), TEMP=str(scratch),
               LAKE_NO_CACHE='1', MATHLIB_NO_CACHE_ON_UPDATE='1')
    tool_hashes = {name: digest(path) for name, path in bins.items()}
    report.update(status='RUNNING', tool_sha256=tool_hashes, dependency_sources=checks)
    try:
        preflight = guarded(project, env, [sys.executable, ROOT / 'tools/comparator-preflight.py', project, bins['landrun']], timeout=60)
        (parent / 'preflight.log').write_text(preflight.stdout + preflight.stderr)
        require(preflight.returncode == 0, 'Runtime preflight failed; inspect preflight.log')
        report['preflight'] = 'PASS'
        chosen = list(enumerate(cases, 1)) if args.case is None else [(args.case, cases[args.case-1])]
        for i, case in chosen:
            started = time.monotonic()
            command = [sys.executable, ROOT / 'tools/comparator-child.py', bindir / 'lake',
                       bins['comparator'], project / case['config']]
            result = guarded(project, env, command)
            output = result.stdout + result.stderr
            logfile = parent / f'case-{i}.log'
            logfile.write_text(output)
            row = dict(production_target=case['production_target'], config=case['config'],
                       seconds=round(time.monotonic()-started, 3),
                       log=logfile.name, log_sha256=digest(logfile))
            row.update(comparison_outcome(result.returncode, output))
            report['cases'].append(row)
            write_json(parent / 'report.json', report)
            require_comparison_success(row)
            print(f'PASS case {i}: Lean + Nanoda + Comparator ({row["seconds"]}s)', flush=True)
        require(all(digest(project / name) == sha for name, sha in packet_hashes.items()), 'Packet changed during checking')
        require(source_manifest() == manifest and input_hashes() == controls, 'Original inputs changed')
        require(check_dependencies(project / '.lake/packages') == checks, 'Copied dependencies changed')
        require(check_dependencies(packages) == checks, 'Original dependencies changed')
        require({name: digest(path) for name, path in bins.items()} == tool_hashes, 'Checker binaries changed')
        report['status'] = 'PASS_ALL_SEVEN' if args.case is None else 'PASS_ONE_CASE_ONLY'
    except BaseException as failure:
        report['status'] = 'FAIL'
        report['failure'] = str(failure)
        raise
    finally:
        report['finished_utc'] = datetime.now(timezone.utc).isoformat()
        write_json(parent / 'report.json', report)
    print('Report: ' + str(parent / 'report.json'), flush=True)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare-only', action='store_true', help='Offline packet construction, no checking')
    parser.add_argument('--tools', type=Path, default=ROOT / '.tools/checkers')
    parser.add_argument('--packages', type=Path)
    parser.add_argument('--lean-bin')
    parser.add_argument('--case', type=int, choices=range(1, 8), help='Smoke test one result, not all-seven acceptance')
    run(parser.parse_args())
