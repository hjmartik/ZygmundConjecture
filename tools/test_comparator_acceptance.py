#!/usr/bin/env python3
"""Fast wrapper regressions; not Lean/kernel execution. Apache-2.0."""
import copy
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
from comparator_runtime import (comparison_outcome, require_comparison_success,
                                external_config, offline_command, runtime_environment, guarded)

SUCCESS = '\n'.join(('Lean default kernel accepts the solution',
                     'nanoda kernel accepts the solution',
                     'con-ron kernel accepts the solution', 'Your solution is okay!'))
CONFIG = dict(challenge_module='Challenge1', solution_module='Solution1',
              theorem_names=['Submitted.target1'], permitted_axioms=['propext', 'Classical.choice', 'Quot.sound'])


class AcceptanceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        parent = Path(__file__).resolve().parents[1] / '.runs'
        parent.mkdir(exist_ok=True)
        cls.work = Path(tempfile.mkdtemp(prefix='wrapper-fixtures-', dir=parent))
        cls.bins = cls.work / 'bin'
        cls.bins.mkdir()
        # These placeholders are never executed; real checker failures are Linux tests.
        for name in ('nanoda_bin', 'con-ron', 'bwrap'):
            path = cls.bins / name
            path.write_text('unit-test placeholder; never executed\n')
            path.chmod(0o700)
        cls.scratch = cls.work / 'scratch'
        cls.scratch.mkdir()

    def test_complete_acceptance(self):
        result = comparison_outcome(0, SUCCESS)
        self.assertTrue(result['passed'])
        require_comparison_success(result)

    def test_each_missing_report(self):
        for line in SUCCESS.splitlines():
            with self.subTest(missing=line):
                outcome = comparison_outcome(0, SUCCESS.replace(line, ''))
                self.assertFalse(outcome['passed'])
                with self.assertRaises(ValueError):
                    require_comparison_success(outcome)

    def test_nonzero_exit_even_after_success_messages(self):
        for code in (1, 73, 124, -9):
            self.assertFalse(comparison_outcome(code, SUCCESS)['passed'])

    def test_substring_is_not_a_report(self):
        self.assertFalse(comparison_outcome(0, '\n'.join('quoted: ' + s for s in SUCCESS.splitlines()))['passed'])

    def test_empty_output(self):
        self.assertFalse(comparison_outcome(0, '')['passed'])

    def test_old_two_kernel_run_not_enough(self):
        self.assertFalse(comparison_outcome(0, SUCCESS.replace('con-ron kernel accepts the solution', ''))['passed'])

    def test_configuration_preserved(self):
        original = copy.deepcopy(CONFIG)
        result = external_config(CONFIG, self.bins)
        self.assertEqual(CONFIG, original)
        self.assertEqual(set(result['external_kernels']), {'nanoda', 'con-ron'})
        self.assertEqual(result['external_kernels']['nanoda'], [str(self.bins / 'nanoda_bin')])

    def test_explicit_nanoda_true_migrates(self):
        result = external_config(dict(CONFIG, enable_nanoda=True), self.bins)
        self.assertNotIn('enable_nanoda', result)
        self.assertIn('con-ron', result['external_kernels'])

    def test_reject_config_overrides(self):
        for changes in (dict(external_kernels={}), dict(enable_nanoda=False),
                        dict(definition_names=['hole']), dict(permitted_axioms=['sorryAx']),
                        dict(theorem_names=[]), dict(theorem_names=['x', 'x']),
                        dict(solution_module='Challenge1'), dict(challenge_module='../escape'),
                        dict(permitted_axioms='propext'), dict(challenge_module=1)):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                external_config(dict(CONFIG, **changes), self.bins)

    def test_missing_checker(self):
        missing = self.work / 'empty-bin'
        missing.mkdir()
        with self.assertRaises(ValueError):
            external_config(CONFIG, missing)

    def test_clean_environment(self):
        with patch.dict(os.environ, LEAN_PATH='untrusted', COMPARATOR_NANODA='override', TOKEN='secret'):
            env = runtime_environment(self.bins, self.scratch, self.bins / 'bwrap')
        for name in ('LEAN_PATH', 'COMPARATOR_NANODA', 'TOKEN'):
            self.assertNotIn(name, env)
        self.assertEqual(env['TMPDIR'], str(self.scratch))

    def test_sandbox_command(self):
        command = offline_command(self.work, self.scratch, self.bins / 'bwrap', ['lake', 'comparator'])
        self.assertIn('--unshare-net', command)
        self.assertIn('--unshare-pid', command)
        self.assertEqual(command[-2:], ['lake', 'comparator'])
        with self.assertRaises(ValueError):
            offline_command('/', self.scratch, self.bins / 'bwrap', ['true'])

    def test_guarded_timeout_stops_owned_unit(self):
        env = runtime_environment(self.bins, self.scratch, self.bins / 'bwrap')
        timeout = subprocess.TimeoutExpired('systemd-run', 40)
        with patch('comparator_runtime.os.geteuid', return_value=501), \
             patch('comparator_runtime.subprocess.run', side_effect=[timeout, subprocess.CompletedProcess([], 0)]) as run:
            with self.assertRaises(subprocess.TimeoutExpired):
                guarded(self.work, env, ['lake', 'comparator'], timeout=10)
        first, second = run.call_args_list
        unit = next(arg.split('=', 1)[1] for arg in first.args[0] if arg.startswith('--unit='))
        self.assertEqual(second.args[0], ['systemctl', '--user', 'stop', unit])
        self.assertIn('--property=RuntimeMaxSec=10', first.args[0])


if __name__ == '__main__':
    unittest.main(verbosity=2)
