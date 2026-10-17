#!/usr/bin/env python3
"""Real checks of the optional unsandboxed runner; not sandbox acceptance. Apache-2.0."""
import argparse
from datetime import datetime, timezone
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
from types import SimpleNamespace

sys.path.insert(0, str(Path(__file__).resolve().parent))
from common import ROOT, LEAN, require, digest, write_json, compiler_bin, fresh_run, source_manifest
from comparator import input_hashes
from comparator_runtime import external_config
from comparator_local import run, run_comparison, tool_paths, local_environment


def main(args):
    require(args.trust_project_code, 'These tests execute without a sandbox; supply --trust-project-code')
    require(platform.system() in {'Darwin', 'Linux'} and os.geteuid() != 0, 'Use an ordinary macOS or Linux account')
    sources = source_manifest()
    controls = {**input_hashes(), **{f'tools/{n}': digest(ROOT / 'tools' / n)
                for n in ('comparator_local.py', 'test_comparator_local.py')}}
    bindir = compiler_bin(args.lean_bin)
    bins = tool_paths(bindir)
    hashes = {name: digest(path) for name, path in bins.items()}
    parent = fresh_run('comparator-local-tests')
    report = dict(status='RUNNING', fixture_only=True, sandboxed=False,
                  started_utc=datetime.now(timezone.utc).isoformat(),
                  platform=platform.system(), architecture=platform.machine(),
                  controls=controls, tools=hashes, cases=[], wrapper_tests=[])
    def save():
        write_json(parent / 'report.json', report)
    print('Unsandboxed test run: ' + str(parent), flush=True)
    save()
    try:
        try:
            run(SimpleNamespace(trust_project_code=False))
        except ValueError as error:
            require('--trust-project-code' in str(error), 'Wrong acknowledgement failure')
        else:
            raise ValueError('Missing trust acknowledgement was accepted')
        report['wrapper_tests'].append('explicit-trust-required')
        env = local_environment(bindir, parent)
        require(not {'LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'COMPARATOR_BWRAP',
                     'SSH_AUTH_SOCK', 'GITHUB_TOKEN'} & env.keys(), 'Unexpected inherited environment')
        require(env['PATH'].split(':')[0] == str(bindir) and env['LEAN_NUM_THREADS'] == '2',
                'Wrong local tool selection or thread setting')
        report['wrapper_tests'].append('controlled-environment-not-a-sandbox')
        challenge = 'theorem answer (n : Nat) : n = n := by sorry\n'
        proof = 'theorem answer (n : Nat) : n = n := rfl\n'
        cases = [
            ('valid', challenge, proof, None),
            ('extra-assumption', challenge,
             'theorem answer (n : Nat) (h : n = n) : n = n := h\n', "Challenge and solution theorem statement do not match: 'answer'"),
            ('changed-definition', 'def number : Nat := 2\ntheorem answer : number = 2 := by sorry\n',
             'def number : Nat := 3\ntheorem answer : number = 3 := rfl\n', "Challenge and solution theorem statement do not match: 'answer'"),
            ('indirect-admission', challenge,
             'theorem helper (n : Nat) : n = n := by sorry\ntheorem answer (n : Nat) : n = n := helper n\n', 'sorryAx'),
            ('custom-axiom', challenge,
             'axiom unjustified (n : Nat) : n = n\ntheorem answer (n : Nat) : n = n := unjustified n\n', 'unjustified'),
            ('missing-nanoda', challenge, proof, 'was not found'),
            ('failing-nanoda', challenge, proof, 'nanoda kernel rejected'),
            ('missing-con-ron', challenge, proof, 'was not found'),
            ('failing-con-ron', challenge, proof, 'con-ron kernel rejected'),
        ]
        for name, statement, solution, rejection in cases:
            project = parent / name
            project.mkdir()
            (project / 'Challenge.lean').write_text(statement)
            (project / 'Solution.lean').write_text(solution)
            shutil.copyfile(LEAN / 'lean-toolchain', project / 'lean-toolchain')
            (project / 'lakefile.toml').write_text('name = "local_checker_tests"\ndefaultTargets = []\n'
                '\n[[lean_lib]]\nname = "Challenge"\n\n[[lean_lib]]\nname = "Solution"\n')
            write_json(project / 'lake-manifest.json', dict(version='1.3.0', packagesDir='.lake/packages',
                       packages=[], name='local_checker_tests', lakeDir='.lake'))
            cfg = external_config(dict(challenge_module='Challenge', solution_module='Solution',
                theorem_names=['answer'], permitted_axioms=['propext', 'Classical.choice', 'Quot.sound']), bindir)
            marker = None
            if name.startswith(('missing-', 'failing-')):
                kernel = name.split('-', 1)[1]
                binary = project / ('fixture-' + name)
                if name.startswith('failing-'):
                    marker = 'LOCAL_FIXTURE_' + kernel.upper().replace('-', '_') + '_EXIT_73'
                    source = project / 'failure.c'
                    source.write_text('#include <stdio.h>\nint main(void) { puts("' + marker + '"); fflush(stdout); return 73; }\n')
                    subprocess.run(['cc', '-O2', '-o', str(binary), str(source)], check=True,
                                   capture_output=True, text=True, timeout=60)
                cfg['external_kernels'][kernel] = [str(binary)]
            config = project / 'config.json'
            write_json(config, cfg)
            frozen = {p.name: digest(p) for p in project.iterdir() if p.is_file()}
            log = parent / (name + '.log')
            row = run_comparison(project, bindir, config, log, timeout=180)
            text = log.read_text()
            row.update(name=name, inputs=frozen, config=cfg, expected_failure=rejection, invocation_marker=marker)
            report['cases'].append(row)
            save()
            if rejection is None:
                require(row['passed'], 'Valid local comparison failed; inspect ' + str(log))
            else:
                require(row['exit_code'] != 0 and not row['comparator_accepted'] and rejection in text,
                        'Rejected for the wrong reason: ' + name)
            if name in ('extra-assumption', 'changed-definition'):
                lines = text.splitlines()
                diagnostic = 'error: ' + rejection
                builds = [i for i, line in enumerate(lines)
                          if line.startswith('Build completed successfully (')]
                errors = [line for line in lines if line.startswith('error:')]
                require(len(builds) == 2 and lines.count(diagnostic) == 1
                        and builds[-1] < lines.index(diagnostic)
                        and errors == [diagnostic] and row['exit_code'] == 1,
                        'Statement-mismatch fixture did not reach the intended comparison: ' + name)
            if marker:
                other = 'con_ron_accepted' if kernel == 'nanoda' else 'nanoda_accepted'
                require(marker in text and row['lean_accepted'] and row[other],
                        'Failure executable did not run alongside successful other kernels')
                row['failure_executable_sha256'] = digest(binary)
            require(all(digest(project / n) == h for n, h in frozen.items()), 'Fixture input changed')
            print('PASS ' + name, flush=True)
            save()
        project = parent / 'timeout'
        project.mkdir()
        fake_bin = project / 'bin'
        fake_bin.mkdir()
        fake_lake = fake_bin / 'lake'
        fake_lake.write_text('#!/bin/sh\nprintf "LOCAL_TIMEOUT_STARTED\\n"\nexec /bin/sleep 30\n')
        fake_lake.chmod(0o700)
        try:
            run_comparison(project, fake_bin, project / 'unused.json', parent / 'timeout.log', timeout=1)
        except subprocess.TimeoutExpired:
            require('LOCAL_TIMEOUT_STARTED' in (parent / 'timeout.log').read_text(), 'Timeout stub did not run')
        else:
            raise ValueError('Timeout was accepted')
        report['wrapper_tests'].append('actual-timeout-is-not-success')
        require(source_manifest() == sources, 'Production sources changed')
        require({**input_hashes(), **{f'tools/{n}': digest(ROOT / 'tools' / n)
                for n in ('comparator_local.py', 'test_comparator_local.py')}} == controls, 'Checking controls changed')
        require({name: digest(path) for name, path in bins.items()} == hashes, 'Tool binaries changed')
        report['status'] = 'PASS_LOCAL_FIXTURES_ONLY'
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
    parser.add_argument('--trust-project-code', action='store_true')
    parser.add_argument('--lean-bin')
    try:
        main(parser.parse_args())
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        parser.exit(1, 'Test failed: ' + str(error) + '\n')
