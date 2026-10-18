"""Regression for the duplicate BudgetExpired class caused by copying the CLI."""
from pathlib import Path
import subprocess
import sys
import unittest
from neighborhood_core import EnhancedSolver
from check_neighborhood_core import instance

HERE=Path(__file__).resolve().parent

class EntryTests(unittest.TestCase):
    def test_initialization_timeout_has_no_traceback(self):
        for variant in ('baseline','joint','cross','both'):
            with self.subTest(variant=variant):
                result=subprocess.run([sys.executable,str(HERE/'run_variant.py'),
                    '--variant',variant,'--seconds','1e-12'],capture_output=True,text=True,timeout=10)
                self.assertEqual(result.returncode,2)
                self.assertIn('Budget expired during initialization',result.stderr)
                self.assertNotIn('Traceback',result.stderr)

    def test_operator_names_and_forced_joint_branch(self):
        for variant in ('joint','cross','both'):
            s=EnhancedSolver(instance(),2,variant=variant)
            self.assertEqual(len(s.destroy_names),4 if variant=='cross' else 5)
            if variant!='cross':
                partial,removed=s.destroy([[0,2,1],[3,4]],4)
                self.assertEqual(s.diagnostics['joint_calls'],1)
                self.assertEqual(sorted([u for r in partial for u in r]+removed),list(range(s.n)))
                self.assertTrue(all(s.valid(r) for r in partial))

if __name__=='__main__':
    unittest.main()
