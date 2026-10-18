import copy
from fractions import Fraction
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import numpy as np
from alns_solver import Solver,atomic_json
from group_neighborhood import GroupSolver
from check_neighborhood_core import instance
from connectivity_bound import build,repaired_certificate,solve,verify
from test_six_hour_queue import warm_record,wait_until
from validate import validate
HERE=Path(__file__).resolve().parent
DATA=json.loads((HERE/'instances.json').read_text())

class ResearchTests(unittest.TestCase):
    def test_group_preserves_tasks_and_seams(self):
        for mode in ('regional','balanced','wide'):
            for seed in range(20):
                solver=GroupSolver(instance(),2,seed,variant=mode)
                original=[[0,2,1],[3,4]]
                partial,removed=solver.destroy(original,4)
                self.assertEqual(sorted(sum(partial,[])+removed),list(range(solver.n)))
                self.assertTrue(all(solver.valid(r) for r in partial))
                repaired=solver.repair(partial,removed,1)
                if repaired:
                    changed=solver.intensify(repaired,20)
                    self.assertEqual(sorted(sum(changed,[])),list(range(solver.n)))
                    self.assertTrue(all(changed) and all(solver.valid(r) for r in changed))
                self.assertEqual(original,[[0,2,1],[3,4]])

    def test_dual_repair_and_tamper(self):
        ins=instance();degree,arcs,cost,upper,_=build(ins,2)
        routes=[[0,2,1],[3,4]];solver=Solver(ins,2)
        actual=(sum(solver.route_time(r) for r in routes)-solver.n*solver.service)*ins['speed_kmh']
        rng=np.random.default_rng(7)
        for _ in range(10):
            cert=repaired_certificate(cost,arcs,upper,degree,[frozenset([1])],rng.normal(0,1e6,len(degree)*2),[12345])
            self.assertLessEqual(float(Fraction(cert['distance_units_fraction']))/1e6,actual+1e-9)
        with tempfile.TemporaryDirectory() as temp:
            record=solve(ins,2,3,Path(temp)/'bound.json')
            self.assertTrue(verify(ins,2,record))
            from verify_bound_certificate import verify as independent_verify
            self.assertTrue(independent_verify(ins,2,record))
            self.assertLessEqual(record['Tmax_lower_h'],max(solver.route_time(r) for r in routes)+1e-9)
            broken=copy.deepcopy(record);broken['certificate']['distance_units_fraction']='123456789'
            with self.assertRaises(ValueError):verify(ins,2,broken)

    def test_queue_kill_pause_resume_and_final(self):
        import os,signal
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);out=root/'run'
            for c,k in [('Case1',3),('Case3',4)]:atomic_json(root/f'{c}.json',warm_record(c,k))
            command=[sys.executable,str(HERE/'run_three_hour_queue.py'),'--out',str(out),
                     '--case1-warm',str(root/'Case1.json'),'--case3-warm',str(root/'Case3.json'),
                     '--hours',str(24/3600),'--bound-seconds','2','--slice-seconds','2','--workers','4','--port','0']
            def state():return json.loads((out/'state.json').read_text())
            with (root/'log').open('w') as log:
                process=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT)
                try:
                    wait_until(lambda:(out/'state.json').exists() and len(state()['jobs'])>=4)
                    duplicate=subprocess.run(command,capture_output=True,text=True,timeout=10)
                    self.assertNotEqual(duplicate.returncode,0)
                    j=next(j for j in state()['jobs'] if j['phase']=='exploration')
                    os.kill(j['pid'],signal.SIGKILL)
                    wait_until(lambda:any(j['status']=='failed' for j in state()['jobs']))
                    process.terminate();process.wait(timeout=20)
                    self.assertEqual(process.returncode,0,(root/'log').read_text())
                    self.assertEqual(state()['status'],'paused');deadline=state()['deadline_unix']
                    process=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT);process.wait(timeout=40)
                    self.assertEqual(process.returncode,0,(root/'log').read_text())
                    self.assertEqual(state()['status'],'completed');self.assertEqual(state()['deadline_unix'],deadline)
                    self.assertEqual(sum(j['phase']=='bound' for j in state()['jobs']),2)
                    self.assertTrue((out/'download_results.zip').exists())
                    for c in ('Case1','Case3'):validate(DATA,json.loads((out/f'best_{c}.json').read_text()))
                finally:
                    if process.poll() is None:process.terminate();process.wait(timeout=20)

if __name__=='__main__':unittest.main()
