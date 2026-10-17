#!/usr/bin/env python3
"""Small fail-closed tests of the public wrapper; no theorem certification. Apache-2.0."""
import io
import json
from contextlib import redirect_stderr
from copy import deepcopy
from pathlib import Path
import sys
import tarfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common as common_module
import comparator as comparator_module
from check import inspect_reports, inspect_replay, replay_groups
from common import ROOT, source_manifest, module_order, targets, ALLOW
from dependencies import inspect_archive, dependency_header, dependency_imports, missing_artifacts
from comparator_runtime import comparison_outcome, require_comparison_success

class CheckerTests(unittest.TestCase):
    def setUp(self):
        self.target = {'name': 'Example.target', 'module': 'Example',
                       'contract': 'Spec.target', 'contract_module': 'Spec'}
        self.report = {'target': 'Example.target', 'module': 'Example', 'contract': 'Spec.target',
                       'contract_module': 'Spec', 'matches': True, 'axioms': sorted(ALLOW)}

    def output(self, *reports):
        return '\n'.join('RZ_REPORT ' + json.dumps(r) for r in reports)

    def test_inventory(self):
        manifest = source_manifest()
        self.assertEqual(len(manifest['sha256']), 409)
        self.assertEqual(len(module_order(manifest)), 404)
        self.assertEqual(len(targets()), 516)

    def test_replay_prefix_groups(self):
        modules = ['Library.Part', 'Library.Part.Inner', 'Library',
                   'LibraryExtra.Result', 'Checks.Contract']
        self.assertEqual(replay_groups(modules), [
            ('Library', {'Library', 'Library.Part', 'Library.Part.Inner'}),
            ('LibraryExtra.Result', {'LibraryExtra.Result'}),
            ('Checks.Contract', {'Checks.Contract'})])
        with self.assertRaisesRegex(ValueError, 'Duplicate replay module'):
            replay_groups(['Library', 'Library'])

    def test_replay_reports_require_exact_unique_coverage(self):
        expected = {'Library', 'Library.Part'}
        self.assertEqual(inspect_replay('replaying Library.Part\nreplaying Library\n', expected),
                         ['Library', 'Library.Part'])
        for output in ['', 'replaying Library\n',
                       'replaying Library\nreplaying Library\n',
                       'replaying Library\nreplaying Library.Part\nreplaying Library.Part\n',
                       'replaying Library\nreplaying LibraryExtra\n',
                       'replaying Library\nreplaying Library.Part\nreplaying Unexpected\n']:
            with self.subTest(output=output), self.assertRaisesRegex(ValueError, 'Replay module coverage'):
                inspect_replay(output, expected)
        with self.assertRaises(ValueError):
            inspect_replay('', set())

    def test_single_module_replay_report(self):
        self.assertEqual(inspect_replay('replaying Library.Part\n', {'Library.Part'}), ['Library.Part'])
        with self.assertRaises(ValueError):
            inspect_replay('replaying Library.Part.Inner\n', {'Library.Part'})

    def test_replay_plan_covers_the_inventory_without_overlap(self):
        modules = module_order(source_manifest())
        groups = replay_groups(modules)
        all_reported = [m for _, group in groups for m in group]
        self.assertEqual(len(all_reported), 404)
        self.assertEqual(set(all_reported), set(modules))
        root = next(group for name, group in groups if name == 'ReyZygmund')
        self.assertIn('ReyZygmund.MathlibOnly.Proof.ProjectedSquareSolutions', root)
        self.assertNotIn('Verification.Inspect', root)
        self.assertEqual(sum(name == 'ReyZygmund' for name, _ in groups), 1)

    def test_mathlib_only_import_boundary(self):
        manifest = source_manifest()
        report = comparator_module.validate_import_separation(manifest)
        self.assertEqual(len(report), 23)
        for i in range(1, 23):
            names = ['Definitions', 'Statements'] if i <= 3 else [
                'Definitions', 'Projections', 'SquareFunctions', 'SupportingStatements']
            self.assertEqual(set(report[f'Challenge{i}']['local_modules']),
                             {f'Challenge{i}', *('ReyZygmund.MathlibOnly.' + n for n in names)})
        real_imports = comparator_module.imports
        for source, forbidden, reason in [
                ('Definitions.lean', 'ReyZygmund.Geometry.Grids', 'Proof-library import'),
                ('SquareFunctions.lean', 'ReyZygmund.Geometry.Grids', 'Proof-library import'),
                ('Projections.lean', 'ReyZygmund.Projection.CrossFiniteSetting', 'Proof-library import'),
                ('SupportingStatements.lean', 'ReyZygmund.MathlibOnly.Solutions', 'Proof-library import'),
                ('Solutions.lean', 'Challenge1', 'Challenge placeholder'),
                ('Solutions.lean', 'Challenge22', 'Challenge placeholder'),
                ('Solutions.lean', 'Verification.Fixtures.IndirectSorry', 'Challenge placeholder'),
                ('Definitions.lean', 'ReyZygmund.Missing', 'Unresolved audit import')]:
            with self.subTest(source=source, forbidden=forbidden), \
                 patch.object(comparator_module, 'imports', side_effect=lambda p, s=source, f=forbidden:
                              [*real_imports(p), f] if p.name == s else real_imports(p)), \
                 self.assertRaisesRegex(ValueError, reason):
                comparator_module.validate_import_separation(manifest)

    def test_exact_specification_closures(self):
        manifest = source_manifest()
        real_imports = comparator_module.imports
        for source, replacement in [
                ('Challenge1.lean', ['ReyZygmund.MathlibOnly.SupportingStatements']),
                ('Challenge22.lean', ['ReyZygmund.MathlibOnly.Statements']),
                ('SupportingStatements.lean', ['ReyZygmund.MathlibOnly.Definitions'])]:
            with self.subTest(source=source), \
                 patch.object(comparator_module, 'imports', side_effect=lambda p, s=source, r=replacement:
                              r if p.name == s else real_imports(p)), \
                 self.assertRaisesRegex(ValueError, 'Independent specification closure differs'):
                comparator_module.validate_import_separation(manifest)

    def test_comparator_input_binding(self):
        cases = comparator_module.validate_cases()
        self.assertEqual(cases[3]['production_target'], 'ReyZygmund.MathlibOnly.rounded_dyadic_endpoint_estimate')
        self.assertEqual(cases[2]['production_target'], 'ReyZygmund.MathlibOnly.zygmund_conjecture')
        real_digest = comparator_module.digest
        for name in ['CASES.json', 'Challenge1.lean', 'Solution.lean', 'comparison-4.json',
                     *(f'Challenge{i}.lean' for i in range(7, 23)),
                     *(f'comparison-{i}.json' for i in range(7, 23))]:
            with self.subTest(name=name), \
                 patch.object(comparator_module, 'digest', side_effect=lambda p, n=name:
                              '0' * 64 if p.name == n else real_digest(p)), \
                 self.assertRaisesRegex(ValueError, 'Reviewed Comparator input differs'):
                comparator_module.validate_cases()

    def test_missing_and_unexpected_adapter(self):
        directory = comparator_module.ADAPTERS
        real_iterdir = Path.iterdir
        actual = list(directory.iterdir())
        for entries in [[p for p in actual if p.name != 'Challenge22.lean'],
                        [*actual, directory / 'Challenge23.lean']]:
            with self.subTest(entries=len(entries)), \
                 patch.object(Path, 'iterdir', lambda p, e=entries:
                              iter(e) if p == directory else real_iterdir(p)), \
                 self.assertRaisesRegex(ValueError, 'Comparator input inventory differs'):
                comparator_module.validate_cases()

    def test_missing_duplicate_unknown_and_reordered_cases(self):
        path = comparator_module.ADAPTERS / 'CASES.json'
        cases = comparator_module.validate_cases()
        variants = [cases[:6], cases[:12], cases[:16], cases[:-1], [*cases[:-1], cases[6]],
                    [*cases[:6], cases[7], cases[6], *cases[8:]]]
        for i in range(6, 22):
            changed = deepcopy(cases)
            changed[i]['production_target'] = 'ReyZygmund.MathlibOnly.unknown'
            variants.append(changed)
        real_read_json = comparator_module.read_json
        for rows in variants:
            with self.subTest(rows=rows), \
                 patch.object(comparator_module, 'read_json', side_effect=lambda p, r=rows:
                              {'cases': r} if p == path else real_read_json(p)), \
                 self.assertRaises(ValueError):
                comparator_module.validate_cases()

    def test_exact_public_names_contracts_and_origins(self):
        registry = targets()
        last = comparator_module.PUBLIC_RESULTS[-1]
        variants = [[r for r in registry if r['name'] != last['name']],
                    [*registry, last],
                    [*registry, {**last, 'name': 'ReyZygmund.MathlibOnly.unknown'}]]
        for target in comparator_module.PUBLIC_RESULTS[6:]:
            for key in ['name', 'contract', 'module', 'contract_module']:
                variants.append([{**r, key: 'Unexpected.origin'} if r['name'] == target['name'] else r
                                 for r in registry])
        for rows in variants:
            with self.subTest(rows=rows[-6:]), \
                 patch.object(comparator_module, 'targets', return_value=rows), \
                 self.assertRaisesRegex(ValueError, 'Public target, contract or defining module differs'):
                comparator_module.validate_cases()

    def test_audited_count_and_specification_metadata(self):
        path = ROOT / 'verification/AUDIT-MANIFEST.json'
        audit = common_module.read_json(path)
        variants = [dict(audit, expected_comparisons=6), dict(audit, expected_comparisons=12), dict(audit, expected_comparisons=16), dict(audit, expected_comparisons=23),
                    dict(audit, specification_modules=audit['specification_modules'][:-1]),
                    dict(audit, specification_closures={})]
        real_read_json = comparator_module.read_json
        for changed in variants:
            with self.subTest(changed=changed), \
                 patch.object(comparator_module, 'read_json', side_effect=lambda p, a=changed:
                              a if p == path else real_read_json(p)), self.assertRaises(ValueError):
                comparator_module.validate_import_separation(source_manifest())

    def test_default_all_twenty_two_and_case_bounds(self):
        cases = comparator_module.validate_cases()
        parser = comparator_module.argument_parser()
        self.assertIsNone(parser.parse_args([]).case)
        selected = comparator_module.selected_cases(cases, parser.parse_args([]).case)
        self.assertEqual([c['id'] for c in selected], [f'main-{i}' for i in range(1, 23)])
        for i in (1, 6, 7, 12, 13, 16, 17, 22):
            number = parser.parse_args(['--case', str(i)]).case
            self.assertEqual(comparator_module.selected_cases(cases, number), [cases[i-1]])
        for value in ('0', '23', '-1', 'unknown'):
            with self.subTest(value=value), redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                parser.parse_args(['--case', value])
        for number in (0, 23, -1, True):
            with self.subTest(number=number), self.assertRaises(ValueError):
                comparator_module.selected_cases(cases, number)

    def test_complete_and_partial_result_labels(self):
        cases = comparator_module.validate_cases()
        success = comparison_outcome(0, '\n'.join([
            'Lean default kernel accepts the solution', 'nanoda kernel accepts the solution',
            'con-ron kernel accepts the solution', 'Your solution is okay!']))
        rows = [{**c, **success} for c in cases]
        self.assertEqual(comparator_module.finish_cases(cases, rows)['status'], 'PASS_ALL_TWENTY_TWO')
        self.assertEqual(comparator_module.finish_cases(cases, rows, unsandboxed=True)['status'],
                         'PASS_ALL_TWENTY_TWO_UNSANDBOXED')
        self.assertEqual(comparator_module.finish_cases(cases, rows[-1:], 22)['status'], 'PASS_ONE_CASE_ONLY')
        for observed in [rows[:6], rows[:12], rows[:16], rows[:-1], rows[-1:], [*rows[:-1], rows[6]],
                         [*rows[:-1], {**rows[-1], 'production_target': 'Unknown.target'}],
                         [*rows[:-1], {**rows[-1], 'passed': False}]]:
            with self.subTest(observed=observed), self.assertRaises(ValueError):
                comparator_module.finish_cases(cases, observed)

    def test_missing_new_module_rejected(self):
        real_is_file = Path.is_file
        for name in ['MathlibOnly/Proof/BoundaryBridge.lean', 'MathlibOnly/Proof/ProjectionDifferencesSolution.lean',
                     'Projection/CrossFiniteSetting.lean', 'MathlibOnly/Projections.lean',
                     'Projection/AveragingFiniteSetting.lean', 'Geometry/PartialSquareFiniteSetting.lean',
                     'Maximal/ProductFiniteSetting.lean', 'MathlibOnly/Proof/AveragingFamilySolutions.lean',
                     'MathlibOnly/Proof/ProjectedSquareSolutions.lean',
                     'Geometry/IcoGrid.lean', 'Geometry/ShiftedGridIco.lean',
                     'Geometry/RoundedSlicesIco.lean', 'MathlibOnly/Proof/CoveringSolution.lean',
                     'MathlibOnly/Proof/SelectionSolution.lean', 'MathlibOnly/Proof/SliceSolutions.lean',
                     'MathlibOnly/Proof/DyadicEndpointSolution.lean']:
            selected = ROOT / 'lean/ReyZygmund' / name
            with self.subTest(name=name), \
                 patch.object(Path, 'is_file', lambda path, s=selected: False if path == s else real_is_file(path)), \
                 self.assertRaisesRegex(ValueError, 'Reviewed source bytes differ'):
                source_manifest()

    def test_source_and_target_manifest_bindings(self):
        real_digest = common_module.digest
        for name, operation in [('SOURCE-MANIFEST.json', source_manifest), ('TARGETS.json', targets)]:
            with self.subTest(name=name), \
                 patch.object(common_module, 'digest', side_effect=lambda p, n=name:
                              '0' * 64 if p.name == n else real_digest(p)), self.assertRaises(ValueError):
                operation()

    def test_changed_and_missing_source_rejected(self):
        manifest = source_manifest()
        selected = ROOT / next(iter(manifest['sha256']))
        real_digest = common_module.digest
        with patch.object(common_module, 'digest',
                          side_effect=lambda path: '0' * 64 if Path(path) == selected else real_digest(path)), \
             self.assertRaisesRegex(ValueError, 'Reviewed source bytes differ'):
            source_manifest()
        real_is_file = Path.is_file
        with patch.object(Path, 'is_file', lambda path: False if path == selected else real_is_file(path)), \
             self.assertRaisesRegex(ValueError, 'Reviewed source bytes differ'):
            source_manifest()

    def test_missing_and_duplicate_target_rejected(self):
        path = ROOT / 'verification/TARGETS.json'
        document = common_module.read_json(path)
        real_read_json = common_module.read_json
        variants = [document['declarations'][:-1],
                    [*document['declarations'][:-1], document['declarations'][0]]]
        for declarations in variants:
            with self.subTest(count=len(declarations)), \
                 patch.object(common_module, 'read_json',
                              side_effect=lambda current, rows=declarations:
                              {'declarations': rows} if Path(current) == path else real_read_json(current)), \
                 self.assertRaises(ValueError):
                targets()

    def test_matching_report(self):
        self.assertEqual(len(inspect_reports(self.output(self.report), [self.target])), 1)

    def test_bad_reports(self):
        variants = [('matches', False), ('target', 'Different.target'), ('module', 'Wrong'),
                    ('contract', 'Wrong.target'), ('contract_module', 'Wrong'),
                    ('axioms', ['sorryAx']), ('axioms', ['Example.unproved'])]
        for key, value in variants:
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                inspect_reports(self.output({**self.report, key: value}), [self.target])

    def test_missing_and_duplicate(self):
        for output in ['', self.output(self.report, self.report)]:
            with self.assertRaises(ValueError):
                inspect_reports(output, [self.target])

    def test_unsafe_archives(self):
        for name, kind in [('../escape', tarfile.REGTYPE), ('/absolute', tarfile.REGTYPE),
                           ('root/device', tarfile.CHRTYPE), ('root/.git/config', tarfile.REGTYPE),
                           ('root/link', tarfile.SYMTYPE)]:
            with self.subTest(name=name):
                stream = io.BytesIO()
                with tarfile.open(fileobj=stream, mode='w') as archive:
                    item = tarfile.TarInfo(name)
                    item.type = kind
                    item.linkname = '../../escape'
                    archive.addfile(item)
                stream.seek(0)
                with tarfile.open(fileobj=stream) as archive, self.assertRaises(ValueError):
                    inspect_archive(archive)

    def test_dependency_headers(self):
        text = ('/- nested /- comment -/ example -/\nmodule\npublic import Mathlib.Example\n'
                'meta import all Lean.Example\n-- ignored\ndef text := "/-"\n')
        self.assertEqual(dependency_imports(text), ['Mathlib.Example', 'Lean.Example'])
        self.assertEqual(dependency_imports('import Foo\n/-! documentation -/\ndef x := 0\n'), ['Foo'])
        self.assertEqual(dependency_header('/- module -/\nimport Foo\ndef x := 0\n'), (['Foo'], False))
        self.assertEqual(dependency_header('/- ignored -/\nmodule\nimport Foo\ndef x := 0\n'), (['Foo'], True))

    def test_dependency_artifact_family(self):
        olean = Path('Fixture.olean')
        names = {'Fixture.olean', 'Fixture.olean.server', 'Fixture.olean.private',
                 'Fixture.ir.sig', 'Fixture.ir'}
        for absent in [None, *sorted(names)]:
            present = names - {absent}
            with self.subTest(absent=absent), patch.object(Path, 'is_file', lambda p: p.name in present):
                self.assertEqual({p.name for p in missing_artifacts(olean, True)}, set() if absent is None else {absent})
        with patch.object(Path, 'is_file', lambda p: p == olean), patch.object(Path, 'exists', lambda p: False):
            self.assertEqual(missing_artifacts(olean, False), [])
        with patch.object(Path, 'is_file', lambda p: p == olean), patch.object(Path, 'exists', lambda p: p.name == 'Fixture.ir.sig'):
            self.assertEqual(missing_artifacts(olean, False), [Path('Fixture.ir')])

    def test_comparator_acceptance(self):
        messages = ['Lean default kernel accepts the solution', 'nanoda kernel accepts the solution', 'con-ron kernel accepts the solution',
                    'Your solution is okay!']
        require_comparison_success(comparison_outcome(0, '\n'.join(messages)))
        for code, output in [(1, '\n'.join(messages))] + [(0, '\n'.join(messages[:i] + messages[i+1:])) for i in range(4)]:
            with self.assertRaises(ValueError):
                require_comparison_success(comparison_outcome(code, output))

if __name__ == '__main__':
    unittest.main(verbosity=2)
