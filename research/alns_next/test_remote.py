"""Integration checks for real subprocesses, not six-hour performance claims."""
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from urllib.request import urlopen

from run_remote import read, web_server
from validate import validate

HERE = Path(__file__).resolve().parent
DATA = json.loads((HERE/'instances.json').read_text())


class RemoteTests(unittest.TestCase):
    def test_http(self):
        with tempfile.TemporaryDirectory() as d:
            out=Path(d)
            (out/'progress.json').write_text('{"status":"testing"}')
            server=web_server(out,0)
            try:
                with urlopen(f'http://127.0.0.1:{server.server_port}/status') as response:
                    self.assertEqual(json.load(response)['status'],'testing')
            finally:
                server.shutdown();server.server_close()

    @unittest.skipUnless(sys.platform.startswith('linux'),'Linux process supervisor')
    def test_killed_child_restarts_and_resume_keeps_archives(self):
        with tempfile.TemporaryDirectory() as d:
            out=Path(d)
            command=[sys.executable,str(HERE/'run_remote.py'),'--output',d,
                '--workers','1','--slice-seconds','30','--snapshot-seconds','2','--port','0']
            process=subprocess.Popen(command,stdout=subprocess.DEVNULL,stderr=subprocess.PIPE)
            try:
                deadline=time.monotonic()+15
                while not (out/'best.json').exists() and time.monotonic()<deadline:
                    time.sleep(.1)
                self.assertTrue((out/'best.json').exists())
                conflict=subprocess.run(command,capture_output=True,timeout=5)
                self.assertNotEqual(conflict.returncode,0)
                progress=read(out/'progress.json')
                self.assertEqual(len(progress['worker_pids']),1)
                os.kill(progress['worker_pids']['0'],signal.SIGKILL)
                deadline=time.monotonic()+12
                while time.monotonic()<deadline:
                    progress=read(out/'progress.json') or {}
                    if progress.get('rounds',{}).get('0',0)>=2 and progress.get('alive_workers')==1:
                        break
                    time.sleep(.1)
                self.assertGreaterEqual(progress.get('rounds',{}).get('0',0),2)
                self.assertGreaterEqual(progress['consecutive_failures'].get('0',0),1)
                process.terminate()
                _,error=process.communicate(timeout=20)
                self.assertEqual(process.returncode,0,error.decode())
                before=read(out/'best.json');validate(DATA,before)
                self.assertTrue(list(out.glob('snapshot_*')))
                resumed=subprocess.run(command+['--run-seconds','2'],capture_output=True,timeout=25)
                self.assertEqual(resumed.returncode,0,resumed.stderr.decode())
                after=read(out/'best.json');validate(DATA,after)
                self.assertLessEqual(after['best_makespan']['Tmax'],before['best_makespan']['Tmax'])
                self.assertLessEqual(after['best_violation']['violation_h'],before['best_violation']['violation_h'])
                self.assertEqual(read(out/'progress.json')['status'],'stopped')
            finally:
                if process.poll() is None:
                    process.kill();process.communicate()


if __name__=='__main__':
    unittest.main()
