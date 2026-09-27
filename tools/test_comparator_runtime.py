#!/usr/bin/env python3
"""Actual Linux Comparator/Nanoda fixtures, isolated from production cases. Apache-2.0."""
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
from common import (ROOT, LEAN, require, digest, read_json, write_json, compiler_bin,
                    source_manifest, targets, fresh_run, control_hashes)
from comparator import input_hashes, validate_cases, tool_paths
from comparator_runtime import guarded, comparison_outcome, require_comparison_success

def main(args):
    require(platform.system() == 'Linux' and os.geteuid() != 0, 'Run as an unprivileged Linux user')
    manifest, selected, controls = source_manifest(), targets(), control_hashes()
    cases, comparator_inputs = validate_cases(), input_hashes()
    bindir = compiler_bin(args.lean_bin)
    bins = tool_paths(args.tools.expanduser().resolve(), bindir)
    hashes = {name: digest(path) for name, path in bins.items()}
    fixtures = ROOT / 'verification/fixtures/comparator'
    fixture_hashes = {p.name: digest(p) for p in fixtures.iterdir() if p.is_file()}
    config = read_json(fixtures / 'config.json')
    require(config['enable_nanoda'] is True and config['permitted_axioms'] == ['propext', 'Classical.choice', 'Quot.sound'],
            'Fixture must require Nanoda and the production axiom allowance')
    run = fresh_run('comparator-fixtures')
    report = dict(status='RUNNING', fixture_only=True, started_utc=datetime.now(timezone.utc).isoformat(),
                  coverage='Five isolated runtime fixtures; no production theorem acceptance',
                  tool_sha256=hashes, fixture_sha256=fixture_hashes, cases=[])
    def save():
        write_json(run / 'report.json', report)
    print('Run: ' + str(run), flush=True)
    save()
    try:
        fixture_cases = [
            ('valid', 'config.json', ['Challenge.lean', 'Solution.lean']),
            ('missing-nanoda', 'config.json', ['Challenge.lean', 'Solution.lean']),
            ('failing-nanoda', 'config.json', ['Challenge.lean', 'Solution.lean']),
            ('changed-definition', 'config-changed-definition.json',
             ['ChallengeChangedDefinition.lean', 'SolutionChangedDefinition.lean']),
            ('indirect-admission', 'config-indirect-admission.json',
             ['AdmissionHelper.lean', 'ChallengeIndirectAdmission.lean', 'SolutionIndirectAdmission.lean']),
        ]
        for name, config_name, modules in fixture_cases:
            project = run / name
            project.mkdir()
            scratch = project / '.lake/verification-tmp'
            scratch.mkdir(parents=True)
            for filename in [*modules, config_name]:
                shutil.copyfile(fixtures / filename, project / filename)
            config_path = project / 'config.json'
            if config_name != 'config.json':
                shutil.copyfile(fixtures / config_name, config_path)
            shutil.copyfile(LEAN / 'lean-toolchain', project / 'lean-toolchain')
            libraries = ''.join('\n[[lean_lib]]\nname = "' + Path(module).stem + '"\n' for module in modules)
            (project / 'lakefile.toml').write_text(
                'name = "packagingFixtures"\ndefaultTargets = []\n' + libraries)
            nanoda = bins['nanoda']
            if name == 'missing-nanoda':
                nanoda = project / 'deliberately-absent-nanoda'
                require(not nanoda.exists(), 'Missing-binary fixture is not missing')
            if name == 'failing-nanoda':
                nanoda = project / 'failing-nanoda'
                # A static binary needs no interpreter/shared-library allowance
                # beyond Comparator's normal narrow Nanoda sandbox.
                result = subprocess.run(['cc', '-O2', '-static', '-o', str(nanoda),
                                         str(fixtures / 'FailingNanoda.c')],
                                        capture_output=True, text=True, timeout=60)
                (run / 'fault-fixture-build.log').write_text(result.stdout + result.stderr)
                require(result.returncode == 0, 'Could not compile the isolated static fault fixture')
            identities = {str(p.relative_to(project)): digest(p) for p in project.iterdir() if p.is_file()}
            env = os.environ.copy()
            for key in ['LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT']:
                env.pop(key, None)
            env.update(PATH=str(bindir) + os.pathsep + env.get('PATH', ''),
                       COMPARATOR_LANDRUN=str(bins['landrun']), COMPARATOR_LEAN4EXPORT=str(bins['lean4export']),
                       COMPARATOR_NANODA=str(nanoda), TMPDIR=str(scratch), TMP=str(scratch), TEMP=str(scratch),
                       LAKE_NO_CACHE='1', MATHLIB_NO_CACHE_ON_UPDATE='1')
            if name == 'valid':
                result = guarded(project, env, [sys.executable, ROOT / 'tools/comparator-preflight.py',
                                               project, bins['landrun']], timeout=60)
                log = run / 'preflight.log'
                log.write_text(result.stdout + result.stderr)
                require(result.returncode == 0, 'Production runtime preflight failed')
                report['preflight_sha256'] = digest(log)
                report['preflight'] = 'PASS'
                save()
            started = time.monotonic()
            result = guarded(project, env, [sys.executable, ROOT / 'tools/comparator-child.py',
                                           bindir / 'lake', bins['comparator'], config_path])
            output = result.stdout + result.stderr
            log = run / (name + '.log')
            log.write_text(output)
            outcome = comparison_outcome(result.returncode, output)
            row = dict(name=name, seconds=round(time.monotonic()-started, 3), log=log.name,
                       log_sha256=digest(log), outcome=outcome)
            report['cases'].append(row)
            save()
            accepted = True
            try:
                require_comparison_success(outcome)
            except ValueError as failure:
                accepted = False
                row['acceptance_rejection'] = str(failure)
            require(accepted == (name == 'valid'), 'Production acceptance returned an unexpected result')
            if name == 'missing-nanoda':
                require(result.returncode != 0 and outcome['lean_accepted'] and not outcome['nanoda_accepted']
                        and 'deliberately-absent-nanoda' in output, 'Missing Nanoda was not the observed failure')
            if name == 'failing-nanoda':
                require(result.returncode != 0 and outcome['lean_accepted'] and not outcome['nanoda_accepted']
                        and 'PACKAGING_FIXTURE_NANODA_FAILURE' in output, 'Failing Nanoda was not actually invoked')
            if name == 'changed-definition':
                require(result.returncode != 0 and 'marker' in output and 'match' in output.lower(),
                        'Changed referenced definition was not the observed rejection')
            if name == 'indirect-admission':
                require(result.returncode != 0 and 'sorryAx' in output,
                        'Indirect admission was not the observed rejection')
            require(all(digest(project / path) == sha for path, sha in identities.items()), 'Fixture inputs changed')
            row['expected_behavior_confirmed'] = True
            save()
            print('PASS fixture: ' + name, flush=True)
        require(source_manifest() == manifest and targets() == selected and control_hashes() == controls,
                'Production inventory, contracts or checker controls changed')
        require(validate_cases() == cases and input_hashes() == comparator_inputs, 'Production Comparator cases changed')
        require({name: digest(path) for name, path in bins.items()} == hashes, 'Installed checker binaries changed')
        require({p.name: digest(p) for p in fixtures.iterdir() if p.is_file()} == fixture_hashes, 'Fixture sources changed')
        report['status'] = 'PASS_FIXTURES_ONLY'
    except BaseException as failure:
        report.update(status='FAIL', failure=str(failure))
        raise
    finally:
        report['finished_utc'] = datetime.now(timezone.utc).isoformat()
        save()
    print('Fixture report: ' + str(run / 'report.json'), flush=True)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tools', type=Path, default=ROOT / '.tools/checkers')
    parser.add_argument('--lean-bin')
    main(parser.parse_args())
