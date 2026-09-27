#!/usr/bin/env python3
"""Small fail-closed tests of the public wrapper; no theorem certification. Apache-2.0."""
import io
import json
from pathlib import Path
import sys
import tarfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common as common_module
import comparator as comparator_module
from check import inspect_reports
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
        self.assertEqual(len(module_order(source_manifest())), 363)
        self.assertEqual(len(targets()), 453)

    def test_mathlib_only_import_boundary(self):
        manifest = source_manifest()
        report = comparator_module.validate_import_separation(manifest)
        self.assertEqual(len(report), 14)
        for i in range(1, 8):
            self.assertEqual(len(report[f'Challenge{i}']['local_modules']), 3)
        real_imports = comparator_module.imports
        for source, forbidden, reason in [
                ('Definitions.lean', 'ReyZygmund.Geometry.Grids', 'Proof-library import'),
                ('SolutionMaximal.lean', 'Challenge1', 'Challenge placeholder'),
                ('Definitions.lean', 'ReyZygmund.Missing', 'Unresolved audit import')]:
            with self.subTest(source=source, forbidden=forbidden), \
                 patch.object(comparator_module, 'imports', side_effect=lambda p, s=source, f=forbidden:
                              [*real_imports(p), f] if p.name == s else real_imports(p)), \
                 self.assertRaisesRegex(ValueError, reason):
                comparator_module.validate_import_separation(manifest)

    def test_comparator_input_binding(self):
        cases = comparator_module.validate_cases()
        self.assertEqual(cases[3]['statement'], 'ReyZygmund.MathlibOnly.RoundedEndpoint')
        self.assertEqual(cases[4]['statement'], 'ReyZygmund.MathlibOnly.ContinuousEndpoint')
        real_digest = comparator_module.digest
        for name in ['CASES.json', 'Challenge1.lean', 'Solution5.lean', 'config-4.json']:
            with self.subTest(name=name), \
                 patch.object(comparator_module, 'digest', side_effect=lambda p, n=name:
                              '0' * 64 if p.name == n else real_digest(p)), \
                 self.assertRaisesRegex(ValueError, 'Reviewed Comparator input differs'):
                comparator_module.validate_cases()

    def test_missing_new_module_rejected(self):
        selected = ROOT / 'lean/ReyZygmund/MathlibOnly/BoundaryBridge.lean'
        real_is_file = Path.is_file
        with patch.object(Path, 'is_file', lambda path: False if path == selected else real_is_file(path)), \
             self.assertRaisesRegex(ValueError, 'Reviewed source bytes differ'):
            source_manifest()

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
        messages = ['Lean default kernel accepts the solution', 'nanoda kernel accepts the solution',
                    'Your solution is okay!']
        require_comparison_success(comparison_outcome(0, '\n'.join(messages)))
        for code, output in [(1, '\n'.join(messages))] + [(0, '\n'.join(messages[:i] + messages[i+1:])) for i in range(3)]:
            with self.assertRaises(ValueError):
                require_comparison_success(comparison_outcome(code, output))

if __name__ == '__main__':
    unittest.main(verbosity=2)
