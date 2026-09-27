#!/usr/bin/env python3
"""Isolated whole-family and sidecar omissions, source recovery, inspection. Apache-2.0."""
import argparse
import os
from pathlib import Path
import shutil
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from common import (ROOT, LEAN, require, digest, source_lock, source_manifest, targets,
                    check_dependencies, compiler_bin, read_json, control_hashes,
                    fresh_run, write_json, lean_env)
from check import Run, inspect_reports
from dependencies import recover, missing_artifacts

MODULE = 'Mathlib.Analysis.SpecialFunctions.Log.Base'
RELATIVE = Path('Mathlib/Analysis/SpecialFunctions/Log/Base.olean')
CASES = [('whole-family', None, 'Base.olean'),
         ('missing-server', 'Base.olean.server', 'Base.olean.server'),
         ('missing-ir', 'Base.ir', 'Base.ir')]

def cache_snapshot(packages):
    """Read-only metadata snapshot; reading a cache may update atime, not mtime."""
    rows = {}
    for item in source_lock()['packages']:
        base = packages / item['name'] / '.lake'
        for directory, _, files in os.walk(base, followlinks=False):
            for name in files:
                path = Path(directory) / name
                stat = path.lstat()
                rows[str(path.relative_to(packages))] = (stat.st_size, stat.st_mtime_ns,
                                                         str(path.readlink()) if path.is_symlink() else None)
    return rows

def run_case(args, case):
    name_of_case, omitted, failed_import = case
    original = args.packages.expanduser().resolve()
    pins = check_dependencies(original)
    manifest, selected, controls = source_manifest(), targets(), control_hashes()
    bindir = compiler_bin(args.lean_bin)
    target = original / 'mathlib/.lake/build/lib/lean' / RELATIVE
    require(not missing_artifacts(target, True), 'Need a complete cached test module')
    cache_before = cache_snapshot(original)
    family = {str(p): digest(p) for p in target.parent.glob('Base.*') if p.is_file()}
    run = Run('recovery-fixture-' + name_of_case, bindir, original)
    run.record.update(fixture_only=True, coverage='Dependency recovery and one fixture; no production theorem acceptance',
                      case=name_of_case, deliberately_missing=omitted or 'whole artifact family',
                      dependency_module=MODULE, original_cache_modified=False)
    packages = run.path / 'packages'
    packages.mkdir()
    print('Preparing isolated cache case: ' + name_of_case, flush=True)
    try:
        for item in source_lock()['packages']:
            name = item['name']
            shutil.copytree(original / name, packages / name, symlinks=True,
                            ignore=shutil.ignore_patterns('.lake'))
            source_cache = original / name / '.lake/build/lib/lean'
            view_cache = packages / name / '.lake/build/lib/lean'
            for directory, dirs, files in os.walk(source_cache, followlinks=False):
                require(not any((Path(directory) / d).is_symlink() for d in dirs), 'Unexpected cache directory symlink')
                relative = Path(directory).relative_to(source_cache)
                destination = view_cache / relative
                destination.mkdir(parents=True, exist_ok=True)
                for filename in files:
                    source = Path(directory) / filename
                    # Selected retained artifacts are real copies, not links:
                    # recovery must be free to replace only these scratch bytes.
                    if name == 'mathlib' and relative == RELATIVE.parent and filename.startswith('Base.'):
                        if omitted is not None and filename != omitted:
                            shutil.copyfile(source, destination / filename)
                        continue
                    (destination / filename).symlink_to(source.resolve())
        require(check_dependencies(packages) == pins, 'Isolated sources differ')
        recovered = packages / 'mathlib/.lake/build/lib/lean' / RELATIVE
        missing = recovered.parent / failed_import
        require(not missing.exists(), 'Test artifact was not omitted')
        require(missing in missing_artifacts(recovered, True), 'Production completeness check missed omission')
        retained = {p.name: digest(p) for p in recovered.parent.glob('Base.*') if p.is_file()}
        if omitted is not None:
            require(recovered.is_file() and Path(str(recovered) + '.private').is_file(),
                    'Partial fixture must preserve the two artifacts checked by the former predicate')
            require(not any(p.is_symlink() for p in recovered.parent.glob('Base.*')), 'Selected artifacts must be copies')
            if name_of_case == 'missing-ir':
                require(recovered.with_suffix('.ir.sig').is_file(), 'IR signature must remain in the missing-IR fixture')
        run.env = lean_env(bindir, packages, run.objects, run.path)
        source = run.path / 'source'
        (source / 'Verification').mkdir(parents=True)
        shutil.copyfile(LEAN / 'Verification/Inspect.lean', source / 'Verification/Inspect.lean')
        fixture = ROOT / 'verification/fixtures/recovery/Recovered.lean'
        shutil.copyfile(fixture, source / 'Recovered.lean')
        run.record['fixture_sha256'] = digest(fixture)
        command = [bindir / 'lean', '-DautoImplicit=false', '-o', run.objects / 'Recovered.olean', 'Recovered.lean']
        try:
            run.command(command, cwd=source)
        except ValueError:
            output = (run.path / run.record['commands'][-1]['log']).read_text()
            require(run.record['commands'][-1]['exit_code'] not in (None, 0)
                    and str(missing) in output,
                    'Pre-recovery failure was not the deliberately absent artifact')
            run.record['missing_artifact_detected'] = True
        else:
            raise ValueError('Fixture unexpectedly compiled without its required artifact')
        receipt_path = recover([MODULE], packages, str(bindir))
        receipt = read_json(receipt_path)
        require(receipt['status'] == 'PASS_DEPENDENCY_RECOVERY'
                and MODULE in {row['module'] for row in receipt['built']}, 'Required artifact was not recovered')
        require(not missing_artifacts(recovered, True) and missing.is_file() and not missing.is_symlink(),
                'Recovery did not create a complete isolated artifact family')
        require({row['module'] for row in receipt['built']} == {MODULE}, 'Unexpected dependency rebuild')
        replaced = {Path(path).name for path in receipt['built'][0]['artifacts']}
        for filename, sha in retained.items():
            if filename in replaced:
                backup = receipt_path.parent / 'previous' / RELATIVE.parent / filename
                require(backup.is_file() and digest(backup) == sha, 'Retained scratch artifact was not preserved in backup')
            else:
                require(digest(recovered.parent / filename) == sha, 'Unreplaced scratch metadata changed')
        run.record['retained_artifact_backups_checked'] = len(set(retained) & replaced)
        run.record['recovery_receipt'] = str(receipt_path)
        run.record['recovery_receipt_sha256'] = digest(receipt_path)
        (run.objects / 'Verification').mkdir(exist_ok=True)
        run.command([bindir / 'lean', '-DautoImplicit=false', '-o', run.objects / 'Verification/Inspect.olean',
                     'Verification/Inspect.lean'], cwd=source)
        run.command(command, cwd=source)
        driver = source / 'InspectRecovered.lean'
        driver.write_text('import Recovered\nimport Verification.Inspect\n'
                          '#rz_verify PackagingRecovery.target against PackagingRecovery.expected\n')
        output = run.command([bindir / 'lean', '-DautoImplicit=false', driver], cwd=source)
        reports = inspect_reports(output, [dict(name='PackagingRecovery.target', module='Recovered',
                                                contract='PackagingRecovery.expected', contract_module='Recovered')])
        run.record['post_recovery_inspection'] = reports
        require(check_dependencies(original) == pins and check_dependencies(packages) == pins, 'Source pins changed')
        require(cache_snapshot(original) == cache_before and all(digest(p) == sha for p, sha in family.items()),
                'Original cache changed during isolated test')
        require(source_manifest() == manifest and targets() == selected and control_hashes() == controls,
                'Production source inventory or checking controls changed')
        require(digest(fixture) == run.record['fixture_sha256'], 'Fixture changed')
        run.record.update(status='PASS_FIXTURES_ONLY', source_pins_preserved=True,
                          original_cache_unchanged=True, production_controls_unchanged=True)
    except BaseException as failure:
        run.record.update(status='FAIL', failure=str(failure))
        raise
    finally:
        run.save()
    print('PASS ' + name_of_case + ': missing artifact detected, recovered offline, and inspected.', flush=True)
    print('Fixture report: ' + str(run.path / 'report.json'), flush=True)
    return run.path / 'report.json'

def main(args):
    suite = fresh_run('recovery-fixtures')
    report = dict(status='RUNNING', fixture_only=True,
                  coverage='Three recovery cases; no production theorem acceptance', cases=[])
    try:
        for case in CASES:
            path = run_case(args, case)
            result = read_json(path)
            require(result['status'] == 'PASS_FIXTURES_ONLY', 'Recovery case did not pass')
            report['cases'].append(dict(name=case[0], report=str(path), report_sha256=digest(path)))
            write_json(suite / 'report.json', report)
        report['status'] = 'PASS_FIXTURES_ONLY'
    except BaseException as failure:
        report.update(status='FAIL', failure=str(failure))
        raise
    finally:
        write_json(suite / 'report.json', report)
    print('PASS all three recovery cases. Suite report: ' + str(suite / 'report.json'), flush=True)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packages', type=Path, required=True, help='Existing complete pinned package cache, read-only')
    parser.add_argument('--lean-bin')
    main(parser.parse_args())
