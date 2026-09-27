#!/usr/bin/env python3
"""Actual Lean fixtures through the production inspector and acceptance code. Apache-2.0."""
import argparse
import json
from pathlib import Path
import shutil
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from common import ROOT, LEAN, source_manifest, targets, compiler_bin, digest, require, write_json, control_hashes
from check import Run, inspect_reports

def main(args):
    manifest, selected, controls = source_manifest(), targets(), control_hashes()
    bindir = compiler_bin(args.lean_bin)
    run = Run('inspection-fixtures', bindir, LEAN / '.lake/packages')
    run.record.update(fixture_only=True, coverage='No production theorem acceptance', cases=[])
    source = run.path / 'source'
    (source / 'Verification').mkdir(parents=True)
    shutil.copyfile(LEAN / 'Verification/Inspect.lean', source / 'Verification/Inspect.lean')
    fixtures = ROOT / 'verification/fixtures/inspection'
    shutil.copytree(fixtures, source / 'PackagingFixtures')
    identities = {str(p.relative_to(ROOT)): digest(p) for p in fixtures.glob('*.lean')}
    run.record['fixture_sha256'] = identities
    def compile_module(module, intentional_warning=False):
        relative = module.replace('.', '/')
        output = run.objects / (relative + '.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        return run.command([bindir / 'lean', '-DautoImplicit=false', '-o', output, relative + '.lean'],
                           cwd=source, warnings=intentional_warning)
    cases = [('Valid', None), ('ReduciblePresentation', None),
             ('LogicallyEquivalent', 'Contract mismatch:'),
             ('IndirectAdmission', 'Unapproved axiom:'),
             ('CustomAxiom', 'Unapproved axiom:'), ('ChangedStatement', 'Contract mismatch:'),
             ('ExtraAssumption', 'Contract mismatch:')]
    try:
        compile_module('Verification.Inspect')
        compile_module('PackagingFixtures.Contracts')
        # The admission is compiled deliberately, then imported through another
        # theorem. The acceptance predicate must discover its transitive sorryAx.
        compile_module('PackagingFixtures.AdmissionHelper', intentional_warning=True)
        compile_module('PackagingFixtures.AxiomHelper')
        for name, rejection in cases:
            module = 'PackagingFixtures.' + name
            compile_module(module)
            contract = ('PackagingFixtures.expectedTrue' if name in
                        {'ReduciblePresentation', 'LogicallyEquivalent'} else 'PackagingFixtures.expected')
            driver = source / ('Inspect' + name + '.lean')
            driver.write_text(f'import {module}\nimport Verification.Inspect\n'
                              f'#rz_verify {module}.target against {contract}\n')
            output = run.command([bindir / 'lean', '-DautoImplicit=false', driver], cwd=source)
            target = dict(name=module + '.target', module=module, contract=contract,
                          contract_module='PackagingFixtures.Contracts')
            raw = [json.loads(line.removeprefix('RZ_REPORT ')) for line in output.splitlines()
                   if line.startswith('RZ_REPORT ')]
            require(len(raw) == 1, 'Expected one actual Lean inspection report')
            outcome = dict(name=name, accepted=False, expected_rejection=rejection, inspection=raw[0])
            try:
                inspect_reports(output, [target])
                outcome['accepted'] = True
            except ValueError as failure:
                outcome['rejection'] = str(failure)
                require(rejection is not None and str(failure).startswith(rejection), 'Rejected for an unexpected reason')
            require(outcome['accepted'] == (rejection is None), 'Fixture acceptance differs from its contract')
            if name == 'Valid':
                wrong = {**target, 'module': 'PackagingFixtures.DeliberatelyWrongOrigin'}
                try:
                    inspect_reports(output, [wrong])
                    raise ValueError('Wrong-origin fixture was unexpectedly accepted')
                except ValueError as failure:
                    require(str(failure).startswith('Wrong declaration origin'),
                            'Wrong-origin fixture reached an unexpected rejection')
                    outcome['wrong_origin_rejection'] = str(failure)
            if name == 'IndirectAdmission':
                require('sorryAx' in raw[0]['axioms'], 'Indirect admission was not actually observed')
            if name == 'CustomAxiom':
                require('PackagingFixtures.AxiomHelper.unproved' in raw[0]['axioms'], 'Custom axiom was not observed')
            run.record['cases'].append(outcome)
            run.save()
            print('PASS fixture: ' + name, flush=True)
        require(source_manifest() == manifest and targets() == selected and control_hashes() == controls,
                'Production source inventory, contracts or checking code changed')
        require({str(p.relative_to(ROOT)): digest(p) for p in fixtures.glob('*.lean')} == identities, 'Fixture files changed')
        run.record['status'] = 'PASS_FIXTURES_ONLY'
    except BaseException as failure:
        run.record.update(status='FAIL', failure=str(failure))
        raise
    finally:
        run.save()
    print('Fixture report: ' + str(run.path / 'report.json'), flush=True)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-bin')
    main(parser.parse_args())
