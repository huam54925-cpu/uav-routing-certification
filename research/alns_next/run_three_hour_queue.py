"""Three-hour research queue: certified connectivity bounds and coupled route search.
Stops COMPUTATION at the deadline; does not stop/delete the cloud instance.
"""
import argparse
import fcntl
import hashlib
import json
import math
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import zipfile
from alns_solver import atomic_json
from run_remote import merge, export_physical, web_server
from validate import validate

HERE = Path(__file__).resolve().parent
VARIANTS = ('baseline', 'both', 'regional', 'balanced', 'wide')
SOURCE_NAMES = ('alns_solver.py', 'neighborhood_core.py', 'run_variant.py',
                'run_remote.py', 'validate.py', 'instances.json', 'run_three_hour_queue.py',
                'run_research_variant.py','group_neighborhood.py','connectivity_bound.py','verify_bound_certificate.py')


def load(path):
    return json.loads(Path(path).read_text())


def read_input(path):
    if zipfile.is_zipfile(path):
        with zipfile.ZipFile(path) as archive:
            names = [n for n in archive.namelist() if n.endswith('/best.json') or n == 'best.json']
            if len(names) != 1:
                raise ValueError('ZIP must contain exactly one best.json')
            return json.loads(archive.read(names[0]))
    return load(path)


def compact_best(result):
    return {k: result[k] for k in ('case', 'fleet', 'instance_sha256', 'status',
                                  'best_makespan', 'best_violation', 'best_feasible')}


def resource_limits():
    available=float(len(os.sched_getaffinity(0)))
    quota=Path('/sys/fs/cgroup/cpu.max')
    if quota.exists():
        q,period=quota.read_text().split()
        if q!='max':available=min(available,int(q)/int(period))
    memory=Path('/sys/fs/cgroup/memory.max')
    cap=memory.read_text().strip() if memory.exists() else 'max'
    return {'cpu_equivalents':available,'memory_bytes':None if cap=='max' else int(cap)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case1-warm', help='Case1 best.json or snapshot ZIP; needed on first launch')
    parser.add_argument('--case3-warm', help='Case3 best.json or snapshot ZIP; needed on first launch')
    parser.add_argument('--out', required=True)
    parser.add_argument('--hours', type=float, default=3)
    parser.add_argument('--bound-seconds', type=float, default=600)
    parser.add_argument('--slice-seconds', type=float, default=600)
    parser.add_argument('--workers', type=int, default=12)
    parser.add_argument('--port', type=int, default=8765, help='localhost only, 0 disables HTTP')
    args = parser.parse_args()
    if (not all(math.isfinite(v) and v > 0 for v in
                (args.hours, args.bound_seconds, args.slice_seconds))
            or args.workers < 4 or not 0 <= args.port <= 65535):
        parser.error('Positive finite budgets, workers >= 4, valid port required')
    resources=resource_limits()
    if args.workers>max(1,math.floor(resources['cpu_equivalents'])):
        parser.error(f'workers exceeds CPU quota: {resources}')
    if resources['memory_bytes'] is not None and resources['memory_bytes']<2*1024**3:
        parser.error('At least 2 GiB container memory needed for this research queue')
    os.environ.update(OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1',MKL_NUM_THREADS='1')
    out = Path(args.out).resolve(); out.mkdir(parents=True, exist_ok=True)
    lock = (out/'queue.lock').open('a')
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        parser.error('Another queue owns this output directory')
    if (out/'STOP').exists():
        parser.error('Remove STOP explicitly before resuming')
    data = load(HERE/'instances.json')
    hashes = {name: hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in SOURCE_NAMES}
    hashes['lower_bounds.py']=hashlib.sha256((HERE.parents[1]/'submission_package/question1/program/src/uav_q1/lower_bounds.py').read_bytes()).hexdigest()
    state_path = out/'state.json'
    if state_path.exists():
        state = load(state_path)
        if state['source_hashes'] != hashes:
            parser.error('Source changed: use a new output directory')
        if state['status'] == 'completed':
            print('Already completed. No tasks relaunched.'); return
        # Refuse overlapping orphan workers after abrupt supervisor death.
        for job in state['jobs']:
            pid = job.get('pid')
            if job['status'] == 'running' and pid:
                cmd = Path(f'/proc/{pid}/cmdline')
                if cmd.exists() and str(out/job['output']).encode() in cmd.read_bytes():
                    parser.error(f'Prior worker {pid} still runs. Wait for its bounded slice to finish, then resume.')
        for job in state['jobs']:
            if job['status'] == 'running':
                job['status'] = 'interrupted'
        # Existing configuration and original deadline take precedence on resume.
    else:
        if not args.case1_warm or not args.case3_warm:
            parser.error('Both snapshot inputs required for first launch')
        for case, fleet, path in [('Case1',3,args.case1_warm), ('Case3',4,args.case3_warm)]:
            record = read_input(path); validate(data,record)
            if (record['case'],record['fleet']) != (case,fleet):
                parser.error(f'Wrong identity for {case}')
            atomic_json(out/f'input_{case}.json',record)
        now=time.time()
        state={'version':1,'status':'starting','started_unix':now,'deadline_unix':now+args.hours*3600,
               'source_hashes':hashes,'bound_seconds':args.bound_seconds,
               'slice_seconds':args.slice_seconds,'workers':args.workers,'jobs':[],
               'promotion':None,'promotion_decided':True,'issues':[],'resources':resources}
        atomic_json(state_path,state)
    initial={c:load(out/f'input_{c}.json') for c in ('Case1','Case3')}
    for record in initial.values(): validate(data,record)
    best={c:compact_best(load(out/f'best_{c}.json')) if (out/f'best_{c}.json').exists()
          else compact_best(initial[c]) for c in initial}
    for record in best.values(): validate(data,record)
    active={}; stop=False; server=None
    deadline=time.monotonic()+max(0,state['deadline_unix']-time.time())

    def request_stop(*_):
        nonlocal stop
        stop=True
    signal.signal(signal.SIGTERM,request_stop);signal.signal(signal.SIGINT,request_stop)

    def collect(job):
        result_path=out/job['output']
        if job['phase']=='bound':
            if not result_path.exists():return None
            from verify_bound_certificate import verify
            record=load(result_path)
            if record.get('certificate') is not None and verify(data['cases'][job['case']],job['fleet'],record):
                atomic_json(out/f'bound_{job["case"]}.json',record)
            return record
        for path in (result_path,Path(str(result_path)+'.checkpoint.json')):
            if path.exists():
                record=load(path);validate(data,record)
                if (record['case'],record['fleet']) != (job['case'],3 if job['case']=='Case1' else 4):
                    raise ValueError('Worker identity mismatch')
                best[job['case']]=compact_best(merge(data,best[job['case']],record))
        return load(result_path) if result_path.exists() else None

    def save_status(status):
        state['status']=status;atomic_json(state_path,state)
        for case,record in best.items():
            atomic_json(out/f'best_{case}.json',record)
            atomic_json(out/f'physical_{case}.json',export_physical(data['cases'][case],record))
        atomic_json(out/'progress.json',{'status':status,'elapsed_hours':(time.time()-state['started_unix'])/3600,
            'remaining_hours':max(0,deadline-time.monotonic())/3600,
            'phase':'exploration' if state['promotion_decided'] else 'paired',
            'alive_workers':sum(p.poll() is None for p,_,_ in active.values()),
            'worker_pids':{str(i):p.pid for i,(p,_,_) in active.items() if p.poll() is None},
            'completed_jobs':sum(j['status']=='done' for j in state['jobs']),
            'failed_jobs':sum(j['status']=='failed' for j in state['jobs']),
            'promotion':state['promotion'],'issues':state['issues'][-5:],
            'bounds':{c:{k:load(out/f'bound_{c}.json')[k] for k in ('Tmax_lower_h','excluded_9h')} for c in best if (out/f'bound_{c}.json').exists()},
            'resources':resources,
            'best':{c:{'Tmax':r['best_makespan']['Tmax'],
                       'best_makespan_violation_h':r['best_makespan']['violation_h'],
                       'best_violation_h':r['best_violation']['violation_h'],'status':r['status']}
                    for c,r in best.items()},'updated_unix':time.time()})
        paired=[{k:j.get(k) for k in ('seed','variant','status','metrics','output','attempt')}
                for j in state['jobs'] if j['phase']=='paired']
        atomic_json(out/'paired_summary.json',paired)

    def launch(phase,case,variant,seed,focus,budget,warm,lane=None,attempt=1):
        index=len(state['jobs'])
        directory=out/f'jobs/{index:05d}_{phase}_{case}_{variant}_{time.time_ns()}'
        directory.mkdir(parents=True,exist_ok=False)
        result=directory/'result.json'
        job={'id':index,'phase':phase,'case':case,'fleet':3 if case=='Case1' else 4,'variant':variant,'seed':seed,'focus':focus,
             'budget_seconds':budget,'lane':lane,'attempt':attempt,'output':str(result.relative_to(out)),
             'truncated_budget':budget < (state['bound_seconds'] if phase=='bound' else state['slice_seconds'])-1e-6,
             'status':'running','launched_unix':time.time()}
        command=[sys.executable,'-u',str(HERE/'run_research_variant.py'),'--variant',variant,
                 '--case',case,'--fleet',str(3 if case=='Case1' else 4),'--seed',str(seed),
                 '--focus',focus,'--seconds',str(budget),'--iterations','1000000000000','--out',str(result)]
        if phase=='bound':
            command=[sys.executable,'-u',str(HERE/'connectivity_bound.py'),'--case',case,
                     '--fleet',str(job['fleet']),'--seconds',str(budget),'--out',str(result)]
        elif warm is not None:
            atomic_json(directory/'warm.json',warm);command+=['--warm',str(directory/'warm.json')]
        job['origin']='cold' if warm is None else 'saved_archive'
        log=(directory/'console.log').open('a')
        try:
            process=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,stdin=subprocess.DEVNULL)
        except OSError as error:
            log.close();job['status']='failed';job['error']=str(error)
        else:
            job['pid']=process.pid;active[index]=(process,log,time.monotonic())
        state['jobs'].append(job);atomic_json(state_path,state)

    # Recover available checkpoints even when a worker was interrupted.
    for job in state['jobs']:
        try: collect(job)
        except (ValueError,KeyError,TypeError,OSError) as error:
            state['issues'].append(f'recovery job {job["id"]}: {error}')
    save_status('starting')
    if args.port: server=web_server(out,args.port)
    next_save=0.;next_snapshot=time.monotonic()+3600
    try:
        while not stop and not (out/'STOP').exists() and time.monotonic()<deadline:
            now=time.monotonic()
            for index,(process,log,launched) in list(active.items()):
                job=state['jobs'][index]
                if process.poll() is None:
                    bound_path=out/f'bound_{job["case"]}.json'
                    if job['phase']=='exploration' and bound_path.exists() and load(bound_path)['excluded_9h']:
                        process.terminate();job['stopped_by_certified_bound']=True
                    if now-launched>job['budget_seconds']+30:
                        process.terminate()
                        job.setdefault('termination_at',now)
                        if now-job['termination_at']>10: process.kill()
                    continue
                log.close();del active[index]
                job['returncode']=process.returncode;job['ended_unix']=time.time()
                try:
                    result=collect(job)
                    if process.returncode!=0 or result is None:
                        raise ValueError(f'exit={process.returncode}, final result present={result is not None}')
                    job['status']='done'
                    job['metrics']={'bound_h':result['Tmax_lower_h']} if job['phase']=='bound' else {'Tmax':result['best_makespan']['Tmax'],
                                    'violation_h':result['best_violation']['violation_h'],
                                    'iterations':result.get('iterations')}
                except (ValueError,KeyError,TypeError,OSError) as error:
                    job['status']='failed';job['error']=str(error)
                    state['issues'].append(f'job {index}: {error}')
            remaining=deadline-time.monotonic()
            if remaining<=.1: break
            for lane in range(state['workers']):
                previous=[j for j in state['jobs'] if j.get('lane')==lane]
                if previous and previous[-1]['status']=='running':continue
                # Two independent lower-bound tasks run once; all freed slots become searches.
                if lane<2 and not previous:
                    case='Case1' if lane==0 else 'Case3'
                    launch('bound',case,'connectivity',0,'max',min(state['bound_seconds'],remaining),None,lane=lane)
                    continue
                case='Case1' if lane>=state['workers']-2 else 'Case3'
                if (out/f'bound_{case}.json').exists() and load(out/f'bound_{case}.json')['excluded_9h']:
                    case='Case3' if case=='Case1' else 'Case1'
                    if (out/f'bound_{case}.json').exists() and load(out/f'bound_{case}.json')['excluded_9h']:
                        continue
                searches=[j for j in previous if j['phase']=='exploration' and j['case']==case]
                variant=VARIANTS[lane%len(VARIANTS)]
                failures=0
                for j in reversed(searches):
                    if j['status']!='failed':break
                    failures+=1
                if failures>=2:variant='baseline'
                if failures>=5:continue
                focus='violation' if lane%4==3 else 'max'
                warm=best[case] if len(searches)%3==0 else initial[case]
                if searches and len(searches)%3!=0:
                    for path in (out/searches[-1]['output'],Path(str(out/searches[-1]['output'])+'.checkpoint.json')):
                        if path.exists():
                            try:
                                candidate=load(path);validate(data,candidate);warm=candidate;break
                            except (ValueError,KeyError,TypeError,OSError):pass
                launch('exploration',case,variant,20261016+lane*100003+len(searches),focus,
                       min(state['slice_seconds'],max(.01,deadline-time.monotonic())),warm,lane=lane)
            if not active:
                state['issues'].append('No pending searches: proven exclusions or exhausted retry limits');stop=True
            if now>=next_save:
                for index in active:
                    try: collect(state['jobs'][index])
                    except (ValueError,KeyError,TypeError,OSError) as error:
                        state['issues'].append(f'checkpoint job {index}: {error}')
                save_status('running');next_save=now+5
            if now>=next_snapshot:
                directory=out/f'snapshot_{time.time_ns()}';directory.mkdir()
                for case in best: atomic_json(directory/f'best_{case}.json',best[case])
                atomic_json(directory/'progress.json',load(out/'progress.json'))
                next_snapshot=now+3600
            time.sleep(.2)
    finally:
        for process,_,_ in active.values():
            if process.poll() is None: process.terminate()
        cleanup_deadline=time.monotonic()+15
        while any(p.poll() is None for p,_,_ in active.values()) and time.monotonic()<cleanup_deadline:
            time.sleep(.1)
        for index,(process,log,_) in active.items():
            if process.poll() is None: process.kill()
            process.wait();log.close()
            state['jobs'][index]['status']='interrupted'
            try: collect(state['jobs'][index])
            except (ValueError,KeyError,TypeError,OSError) as error: state['issues'].append(str(error))
        active.clear()
        save_status('completed' if time.monotonic()>=deadline else 'paused')
        directory=out/f'final_{time.time_ns()}';directory.mkdir()
        for case in best:
            atomic_json(directory/f'best_{case}.json',best[case])
            atomic_json(directory/f'physical_{case}.json',export_physical(data['cases'][case],best[case]))
        atomic_json(directory/'progress.json',load(out/'progress.json'))
        with zipfile.ZipFile(out/'download_results.zip','w',zipfile.ZIP_DEFLATED) as archive:
            for path in out.rglob('*'):
                if path.is_file() and path.name not in ('download_results.zip','queue.lock','console.log'):
                    archive.write(path,str(path.relative_to(out)))
        if server: server.shutdown();server.server_close()
        print(f'Queue {state["status"]}. Results: {out}. Cloud instance is NOT powered off.',flush=True)
        fcntl.flock(lock,fcntl.LOCK_UN);lock.close()


if __name__=='__main__':
    main()
