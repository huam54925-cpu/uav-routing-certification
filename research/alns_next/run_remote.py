"""Linux unattended ALNS supervisor. Six hours creates a snapshot, never powers off."""
import argparse
from collections import Counter
import fcntl
import hashlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import threading
import time

from alns_solver import Solver, atomic_json
from validate import validate

HERE = Path(__file__).resolve().parent


def read(path):
    try:
        return json.loads(Path(path).read_text(encoding='utf-8'))
    except (OSError, ValueError):
        return None


def merge(data, left, right):
    """Never lose a feasible witness when a worker restarts from another archive."""
    validate(data, right)
    if left is None:
        left = dict(right)
    if (left['case'], left['fleet'], left['instance_sha256']) != (
        right['case'], right['fleet'], right['instance_sha256']
    ):
        raise ValueError('Archive identity mismatch')
    keys = {
        'best_makespan': lambda r: (r['Tmax'], r['violation_h'], r['total_h']),
        'best_violation': lambda r: (r['violation_h'], r['Tmax'], r['total_h']),
        'best_feasible': lambda r: (r['Tmax'], r['total_h']),
    }
    for name, key in keys.items():
        candidate = right.get(name)
        if candidate and (left.get(name) is None or key(candidate) < key(left[name])):
            left[name] = candidate
    left['status'] = 'FEASIBLE' if left.get('best_feasible') else 'UNKNOWN'
    # Current/iterations/history belong to individual slices, not the aggregate.
    for name in ('current', 'weights', 'operator_stats', 'history', 'iterations',
                 'elapsed_seconds', 'initial_Tmax', 'seed'):
        left.pop(name, None)
    validate(data, left)
    return left


def export_physical(instance, result):
    copies = [p for p in instance['points'] for _ in range(p['visits'])]
    archives = {}
    for name in ('best_makespan', 'best_violation', 'best_feasible'):
        item = result.get(name)
        if item is None:
            archives[name] = None
            continue
        routes = []
        for k, (route, hours) in enumerate(zip(item['routes'], item['times_h']), 1):
            routes.append({'uav': k, 'sequence': [0] + [copies[u]['id'] for u in route] + [0],
                           'time_h': hours, 'service_count': len(route)})
        archives[name] = {**{k:v for k,v in item.items() if k != 'routes'}, 'routes': routes}
    return {'case': result['case'], 'fleet': result['fleet'], 'status': result['status'],
            'instance_sha256': result['instance_sha256'], 'archives': archives,
            'optimality_proven': False}


def web_server(out, port):
    class Handler(BaseHTTPRequestHandler):
        def do_GET(self):
            if self.path == '/status':
                payload = (out / 'progress.json').read_bytes()
                kind = 'application/json'
            else:
                payload = b'''<!doctype html><meta charset="utf-8"><title>ALNS</title>
<h2>ALNS live progress</h2><pre id="p"></pre><script>
async function refresh(){try{let r=await fetch('/status',{cache:'no-store'});
document.getElementById('p').textContent=JSON.stringify(await r.json(),null,2)}
catch(e){document.getElementById('p').textContent=String(e)}}
refresh();setInterval(refresh,5000);</script>'''
                kind = 'text/html; charset=utf-8'
            self.send_response(200)
            self.send_header('Content-Type', kind)
            self.end_headers()
            self.wfile.write(payload)

        def log_message(self, *args):
            pass
    server = ThreadingHTTPServer(('127.0.0.1', port), Handler)
    threading.Thread(target=server.serve_forever, daemon=True).start()
    return server


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--data', default=str(HERE / 'instances.json'))
    p.add_argument('--case', default='Case1')
    p.add_argument('--fleet', type=int, default=3)
    p.add_argument('--workers', type=int, default=8)
    p.add_argument('--slice-seconds', type=float, default=600)
    p.add_argument('--snapshot-seconds', type=float, default=21600)
    p.add_argument('--run-seconds', type=float, default=0, help='0 = continue until STOP/signal')
    p.add_argument('--seed', type=int, default=20261015)
    p.add_argument('--warm', help='An output/checkpoint from alns_solver.py, same instance/fleet')
    p.add_argument('--output', default='runs/case1_n3')
    p.add_argument('--port', type=int, default=8765, help='0 disables HTTP; otherwise localhost only')
    a = p.parse_args()
    if (a.workers < 1 or a.fleet < 1 or not a.slice_seconds >= 2 or
        not a.snapshot_seconds > 0 or not a.run_seconds >= 0 or not 0 <= a.port <= 65535 or
        not all(math_isfinite(x) for x in (a.slice_seconds,a.snapshot_seconds,a.run_seconds))):
        p.error('Invalid worker count, budget, fleet, or port')
    data = json.loads(Path(a.data).read_text(encoding='utf-8'))
    instance = data['cases'][a.case]
    solver = Solver(instance, a.fleet)
    if a.fleet > solver.n:
        p.error('Fleet exceeds task copies')
    out = Path(a.output).resolve()
    out.mkdir(parents=True, exist_ok=True)
    lock = (out / 'supervisor.lock').open('a')
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        p.error('Another supervisor already owns this output directory')
    if (out / 'STOP').exists():
        p.error('STOP exists; remove it explicitly before resuming')
    identity = {'case':a.case,'fleet':a.fleet,'instance_sha256':solver.fingerprint}
    meta = read(out / 'run.json')
    if meta and any(meta.get(k) != v for k,v in identity.items()):
        p.error('Output directory belongs to another instance/fleet')
    best = read(out / 'best.json')
    if best:
        validate(data, best)
        if any(best.get(k) != v for k,v in identity.items()):
            p.error('Saved best has a different identity')
    if a.warm:
        warm = json.loads(Path(a.warm).read_text(encoding='utf-8'))
        if any(warm.get(k) != v for k,v in identity.items()):
            p.error('Warm-start identity mismatch')
        best = merge(data, best, warm)
    # Recover completed checkpoints even if the prior supervisor died before aggregation.
    for path in out.glob('worker_*.json*'):
        if not path.name.endswith(('.json', '.checkpoint.json')):
            continue
        saved = read(path)
        if saved:
            best = merge(data, best, saved)
    atomic_json(out / 'run.json', {**identity, 'workers':a.workers,
        'source_sha256':hashlib.sha256((HERE/'alns_solver.py').read_bytes()).hexdigest(),
        'updated_unix':time.time()})
    atomic_json(out / 'progress.json', {'status':'starting', **identity})
    server = web_server(out,a.port) if a.port else None  # Fail on occupied port before spawning.
    stop = False
    def request_stop(*_):
        nonlocal stop
        stop = True
    signal.signal(signal.SIGTERM, request_stop)
    signal.signal(signal.SIGINT, request_stop)
    started = time.monotonic()
    next_snapshot = started + a.snapshot_seconds
    slots = {}
    rounds = Counter()
    failures = Counter()
    retry_at = Counter()
    issue = None
    if best:
        atomic_json(out/'best.json',best)

    def collect():
        nonlocal best, issue
        for wid in range(a.workers):
            for path in (out/f'worker_{wid:02d}.json', out/f'worker_{wid:02d}.json.checkpoint.json'):
                record = read(path)
                if record:
                    try:
                        best = merge(data,best,record)
                    except ValueError as error:
                        issue = f'{path.name}: {error}'
        if best:
            atomic_json(out/'best.json',best)
            atomic_json(out/'best_physical.json',export_physical(instance,best))

    try:
        while not stop and not (out/'STOP').exists():
            now = time.monotonic()
            collect()
            if a.run_seconds and now-started >= a.run_seconds:
                break
            for wid in range(a.workers):
                slot = slots.get(wid)
                if slot:
                    process, launched, log, killed = slot
                    if process.poll() is None:
                        # A hung iteration cannot hold the entire six-hour run hostage.
                        if now-launched > a.slice_seconds+60 and not killed:
                            process.terminate()
                            slots[wid] = (process,launched,log,now)
                        elif killed and now-killed > 10:
                            process.kill()
                        continue
                    log.close()
                    if process.returncode != 0 or killed:
                        failures[wid] += 1
                        retry_at[wid] = now + min(300, 2**min(failures[wid],8))
                        issue = f'worker {wid}: exit {process.returncode}; see worker_{wid:02d}.log'
                    else:
                        failures[wid] = 0
                    slots.pop(wid)
                if now < retry_at[wid]:
                    continue
                rounds[wid] += 1
                focus = 'max' if wid%2 == 0 else 'violation'
                command = [sys.executable,'-u',str(HERE/'alns_solver.py'),
                    '--data',str(Path(a.data).resolve()),'--case',a.case,'--fleet',str(a.fleet),
                    '--focus',focus,'--seconds',str(a.slice_seconds),'--iterations','1000000000000',
                    '--seed',str(a.seed+wid*1000003+time.time_ns()%1000000000),
                    '--out',str(out/f'worker_{wid:02d}.json')]
                if best:
                    # Dedicated immutable warm input: the parent may update best.json meanwhile.
                    warm_path=out/f'warm_{wid:02d}.json'
                    atomic_json(warm_path,best)
                    command += ['--warm',str(warm_path)]
                log=(out/f'worker_{wid:02d}.log').open('a',buffering=1)
                try:
                    process=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,stdin=subprocess.DEVNULL)
                except Exception:
                    log.close()
                    raise
                slots[wid]=(process,now,log,None)
            alive=sum(s[0].poll() is None for s in slots.values())
            progress={'status':'running' if alive else 'retrying',**identity,
                'elapsed_hours':round((now-started)/3600,4),'alive_workers':alive,
                'workers_requested':a.workers,'rounds':dict(rounds),'consecutive_failures':dict(failures),
                'worker_pids':{str(wid):slot[0].pid for wid,slot in slots.items() if slot[0].poll() is None},
                'last_issue':issue,'updated_unix':time.time(),
                'best': {name:({k:v for k,v in best[name].items() if k!='routes'} if best.get(name) else None)
                    for name in ('best_makespan','best_violation','best_feasible')} if best else None,
                'checkpoints':{str(wid): (round(time.time()-path.stat().st_mtime,1) if path.exists() else None)
                    for wid in range(a.workers) for path in [out/f'worker_{wid:02d}.json.checkpoint.json']}}
            atomic_json(out/'progress.json',progress)
            if now>=next_snapshot:
                snapshot=out/f'snapshot_{time.time_ns()}'
                snapshot.mkdir()
                for path in out.glob('*.json'):
                    saved=read(path)
                    if saved is not None:
                        atomic_json(snapshot/path.name,saved)
                next_snapshot=now+a.snapshot_seconds
            print(json.dumps(progress),flush=True)
            time.sleep(1)
    finally:
        for process,_,_,_ in slots.values():
            if process.poll() is None:
                process.terminate()
        deadline=time.monotonic()+15
        while any(s[0].poll() is None for s in slots.values()) and time.monotonic()<deadline:
            time.sleep(.1)
        for process,_,log,_ in slots.values():
            if process.poll() is None:
                process.kill()
            process.wait()
            log.close()
        collect()
        atomic_json(out/'progress.json',{'status':'stopped',**identity,'updated_unix':time.time(),
            'elapsed_hours':(time.monotonic()-started)/3600,'has_saved_result':best is not None})
        if server:
            server.shutdown()
            server.server_close()
        fcntl.flock(lock,fcntl.LOCK_UN)
        lock.close()


def math_isfinite(x):
    return x == x and abs(x) != float('inf')


if __name__=='__main__':
    main()
