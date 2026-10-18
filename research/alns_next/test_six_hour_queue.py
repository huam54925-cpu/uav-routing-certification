"""Short real-process tests; do not represent six-hour performance evidence."""
import json
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from alns_solver import Solver, atomic_json
from run_six_hour_queue import choose_variant
from validate import validate
HERE=Path(__file__).resolve().parent
DATA=json.loads((HERE/'instances.json').read_text())

def warm_record(case,k):
    solver=Solver(DATA['cases'][case],k)
    routes=[list(range(i,solver.n,k)) for i in range(k)]
    t,v,total,ts=solver.metrics(routes)
    item={'routes':routes,'Tmax':t,'violation_h':v,'total_h':total,'times_h':ts}
    result={'case':case,'fleet':k,'instance_sha256':solver.fingerprint,
            'status':'FEASIBLE' if t<=9 else 'UNKNOWN','best_makespan':item,
            'best_violation':item,'best_feasible':item if t<=9 else None}
    validate(DATA,result);return result

def wait_until(check,seconds=10):
    end=time.monotonic()+seconds
    while time.monotonic()<end:
        if check(): return
        time.sleep(.1)
    raise AssertionError('Timed out waiting for state')

class QueueTests(unittest.TestCase):
    def test_promotion_requires_two_paired_improvements(self):
        jobs=[]
        for seed in (0,1,2):
            for variant,value in [('baseline',10.),('joint',9.8 if seed==0 else 10.),('cross',9.9)]:
                jobs.append({'seed':seed,'variant':variant,'phase':'paired','status':'done','metrics':{'Tmax':value}})
        self.assertEqual(choose_variant(jobs,10.),'cross')
        self.assertIsNone(choose_variant(jobs,9.))

    @unittest.skipUnless(sys.platform.startswith('linux'),'Linux queue')
    def test_killed_worker_pause_resume_deadline_and_archives(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);out=root/'run'
            for case,k in [('Case1',3),('Case3',4)]: atomic_json(root/f'{case}.json',warm_record(case,k))
            command=[sys.executable,str(HERE/'run_six_hour_queue.py'),'--out',str(out),
                     '--case1-warm',str(root/'Case1.json'),'--case3-warm',str(root/'Case3.json'),
                     '--hours',str(25/3600),'--paired-seconds','2','--slice-seconds','2',
                     '--workers','4','--port','0']
            def state(): return json.loads((out/'state.json').read_text())
            with (root/'log').open('w') as log:
                process=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT)
                try:
                    wait_until(lambda:(out/'state.json').exists() and any(j.get('pid') for j in state()['jobs']))
                    duplicate=subprocess.run(command,capture_output=True,text=True,timeout=5)
                    self.assertNotEqual(duplicate.returncode,0)
                    self.assertIn('Another queue owns',duplicate.stderr)
                    pid=next(j['pid'] for j in state()['jobs'] if j.get('pid'))
                    import os
                    os.kill(pid,signal.SIGKILL)
                    wait_until(lambda:any(j['status']=='failed' for j in state()['jobs']))
                    process.terminate();process.wait(timeout=20)
                    self.assertEqual(process.returncode,0)
                    self.assertEqual(state()['status'],'paused')
                    before={c:json.loads((out/f'best_{c}.json').read_text()) for c in ('Case1','Case3')}
                    saved_deadline=state()['deadline_unix']
                    process=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT)
                    process.wait(timeout=40)
                    self.assertEqual(process.returncode,0,(root/'log').read_text())
                    final=state();self.assertEqual(final['status'],'completed')
                    self.assertEqual(final['deadline_unix'],saved_deadline)
                    self.assertTrue(any(j['phase']=='exploration' for j in final['jobs']))
                    for c in ('Case1','Case3'):
                        after=json.loads((out/f'best_{c}.json').read_text());validate(DATA,after)
                        self.assertLessEqual(after['best_makespan']['Tmax'],before[c]['best_makespan']['Tmax'])
                    self.assertTrue(list(out.glob('final_*')))
                    done=subprocess.run(command,capture_output=True,text=True,timeout=5)
                    self.assertEqual(done.returncode,0)
                    self.assertIn('Already completed',done.stdout)
                finally:
                    if process.poll() is None:
                        process.terminate();process.wait(timeout=20)

if __name__=='__main__': unittest.main()
