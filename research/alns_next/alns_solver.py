"""Fixed-fleet repeated-inspection ALNS research prototype (stdlib only)."""
import argparse
import hashlib
import json
import math
import random
import os
import signal
import time
from pathlib import Path


def atomic_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + '.tmp')
    with tmp.open('w', encoding='utf-8') as stream:
        json.dump(value, stream, indent=2, allow_nan=False)
        stream.flush()
        os.fsync(stream.fileno())
    tmp.replace(path)


class BudgetExpired(Exception):
    pass


class Solver:
    destroy_names = ("random", "bottleneck", "spatial", "segment")

    def __init__(self, instance, fleet=3, seed=0, focus='max'):
        self.data, self.k = instance, fleet
        self.case = None
        self.fingerprint = hashlib.sha256(json.dumps(instance,sort_keys=True).encode()).hexdigest()
        self.rng = random.Random(seed)
        self.focus = focus
        self.physical, self.xy = [], [(0., 0.)]
        for p in instance['points']:
            self.xy.append((p['x'], p['y']))
            self.physical.extend([len(self.xy)-1] * p['visits'])
        self.n = len(self.physical)
        self.travel = [[math.dist(a,b)*instance['unit_km']/instance['speed_kmh']
                        for b in self.xy] for a in self.xy]
        self.service, self.limit = instance['service_h'], instance['limit_h']
        self.deadline = float('inf')
        self.stop_requested = False

    def check_time(self):
        if self.stop_requested or time.monotonic() >= self.deadline:
            raise BudgetExpired

    def valid(self, r):
        return all(self.physical[a] != self.physical[b] for a,b in zip(r,r[1:]))

    def route_time(self, r):
        nodes = [0] + [self.physical[u] for u in r] + [0]
        return sum(self.travel[a][b] for a,b in zip(nodes,nodes[1:])) + len(r)*self.service

    def metrics(self, routes):
        ts = [self.route_time(r) for r in routes]
        return max(ts), sum(max(0,t-self.limit) for t in ts), sum(ts), ts

    def score_times(self, ts):
        v = sum(max(0,t-self.limit) for t in ts)
        return max(ts) + (2. if self.focus == 'violation' else .25)*v + .001*sum(ts)

    def score(self, routes):
        return self.score_times([self.route_time(r) for r in routes])

    def repair(self, routes, removed, mode):
        routes = [r[:] for r in routes]
        todo = list(removed)
        while todo:
            self.check_time()
            ts = [self.route_time(r) for r in routes]
            choices = []
            for u in todo:
                node = self.physical[u]
                options = []
                for k,r in enumerate(routes):
                    for pos in range(len(r)+1):
                        a = self.physical[r[pos-1]] if pos else 0
                        b = self.physical[r[pos]] if pos < len(r) else 0
                        if node in (a,b):
                            continue
                        dt = self.travel[a][node]+self.travel[node][b]-self.travel[a][b]+self.service
                        nts = ts[:]; nts[k] += dt
                        options.append((self.score_times(nts), nts[k], k, pos))
                if not options:
                    return None  # Reject this whole iteration; never add a vehicle.
                options.sort()
                regret = options[1][0]-options[0][0] if len(options)>1 else float('inf')
                key = (-regret, options[0][0], u) if mode == 1 else (options[0][0], options[0][1], u)
                choices.append((key, u, options[0]))
            _, u, (_, _, k, pos) = min(choices)
            routes[k].insert(pos,u); todo.remove(u)
        return routes if all(routes) else None

    def destroy(self, routes, mode):
        flat = [u for r in routes for u in r]
        q = self.rng.randint(max(2,self.n//10), max(2,self.n//3))
        if mode == 0:
            removed = set(self.rng.sample(flat,min(q,len(flat))))
        elif mode == 1:
            bottleneck = max(routes,key=self.route_time)
            removed = set(self.rng.sample(bottleneck,min(q,len(bottleneck))))
        elif mode == 2:
            center = self.physical[self.rng.choice(flat)]
            order = sorted(flat,key=lambda u:self.travel[center][self.physical[u]]*(.8+.4*self.rng.random()))
            removed = set(order[:q])
        else:
            r = self.rng.choice([r for r in routes if r])
            start = self.rng.randrange(len(r))
            removed = set(r[start:start+q])
        partial = []
        for r in routes:
            kept = []
            for u in r:
                if u in removed:
                    continue
                # Removing a separator can expose equal physical neighbors.
                if kept and self.physical[kept[-1]] == self.physical[u]:
                    removed.add(u)
                else:
                    kept.append(u)
            partial.append(kept)
        return partial, sorted(removed)

    def intensify(self, routes, trials=250):
        routes = [r[:] for r in routes]; score = self.score(routes)
        for _ in range(trials):
            self.check_time()
            a,b = self.rng.sample(range(self.k),2) if self.k>1 else (0,0)
            candidate = [r[:] for r in routes]
            mode = self.rng.randrange(3)
            if mode == 0:  # Intra-route 2-opt.
                if len(candidate[a]) < 2: continue
                i,j = sorted(self.rng.sample(range(len(candidate[a])),2))
                candidate[a][i:j+1] = reversed(candidate[a][i:j+1])
            elif mode == 1:  # Cross-route 2-opt*: exchange complete tails.
                if a == b: continue
                i = self.rng.randrange(len(candidate[a])+1)
                j = self.rng.randrange(len(candidate[b])+1)
                ra,rb = candidate[a],candidate[b]
                candidate[a],candidate[b] = ra[:i]+rb[j:], rb[:j]+ra[i:]
            else:  # Or-opt of length 2 or 3; source seam checked below.
                length = self.rng.choice([2,3])
                if len(candidate[a]) < length: continue
                i = self.rng.randrange(len(candidate[a])-length+1)
                block = candidate[a][i:i+length]; del candidate[a][i:i+length]
                j = self.rng.randrange(len(candidate[b])+1)
                candidate[b][j:j] = block
            if not all(candidate) or not all(self.valid(r) for r in candidate): continue
            value = self.score(candidate)
            if value < score-1e-12:
                routes,score = candidate,value
        return routes

    def solve(self, seconds, iterations, warm=None, checkpoint=None, archives=None):
        started = time.monotonic(); self.deadline = started+seconds
        if warm is None:
            # Random singleton anchors diversify the otherwise deterministic repair.
            anchors = self.rng.sample(range(self.n),self.k)
            current = self.repair([[u] for u in anchors], [u for u in range(self.n) if u not in anchors],1)
            if current is None: raise ValueError('Initial repair failed; try another seed.')
        else:
            current = [r[:] for r in warm]
        if len(current)!=self.k or sorted(u for r in current for u in r)!=list(range(self.n)) or not all(current) or not all(self.valid(r) for r in current):
            raise ValueError('Invalid initial solution')
        best_max = [r[:] for r in current]; best_v = [r[:] for r in current]
        best_feasible = current if self.metrics(current)[0] <= self.limit+1e-9 else None
        if archives:
            for name in ('best_makespan', 'best_violation', 'best_feasible'):
                item = archives.get(name)
                if item is None:
                    continue
                r = item['routes']
                if (len(r) != self.k or not all(r) or
                    sorted(u for route in r for u in route) != list(range(self.n)) or
                    not all(self.valid(route) for route in r)):
                    raise ValueError('Invalid archived solution')
                m = self.metrics(r)
                if m[:3] < self.metrics(best_max)[:3]:
                    best_max = [route[:] for route in r]
                bv = self.metrics(best_v)
                if (m[1],m[0],m[2]) < (bv[1],bv[0],bv[2]):
                    best_v = [route[:] for route in r]
                if m[0] <= self.limit+1e-9 and (best_feasible is None or m[0] < self.metrics(best_feasible)[0]):
                    best_feasible = [route[:] for route in r]
        weights = [1.]*(2*len(self.destroy_names))
        stats = [{'attempts':0,'accepted':0,'archive_improvements':0,'repair_failures':0,'repair_successes':0,'destroy_repair_seconds':0.,'intensify_seconds':0.} for _ in weights]
        history = []; completed = 0; last_save = started
        initial_max = self.metrics(current)[0]
        def snapshot():
            def record(routes):
                if routes is None: return None
                t,v,total,ts = self.metrics(routes)
                return {'routes':routes,'Tmax':t,'violation_h':v,'total_h':total,'times_h':ts}
            return {'case':self.case,'instance_sha256':self.fingerprint,'fleet':self.k,'focus':self.focus,'elapsed_seconds':time.monotonic()-started,
                    'iterations':completed,'initial_Tmax':initial_max,'best_makespan':record(best_max),
                    'best_violation':record(best_v),'best_feasible':record(best_feasible),
                    'current':record(current),'weights':weights,'operator_stats':stats,'history':history,
                    'operator_names':[d+'/'+r for d in self.destroy_names for r in ('greedy','regret2')],
                    'diagnostics':getattr(self, 'diagnostics', {}),
                    'variant':getattr(self, 'variant', 'baseline'),
                    'status':'FEASIBLE' if best_feasible is not None else 'UNKNOWN'}
        def save():
            if checkpoint:
                atomic_json(checkpoint, snapshot())
        save()  # Preserve a complete initial witness before entering the loop.
        try:
            for it in range(iterations):
                self.check_time()
                idx = self.rng.choices(range(len(weights)),weights=weights,k=1)[0]
                stats[idx]['attempts'] += 1
                phase_started = time.monotonic()
                try:
                    partial, removed = self.destroy(current,idx//2)
                    candidate = self.repair(partial,removed,idx%2)
                finally:
                    stats[idx]['destroy_repair_seconds'] += time.monotonic()-phase_started
                completed += 1
                reward = .1
                if candidate is None:
                    stats[idx]['repair_failures'] += 1
                else:
                    stats[idx]['repair_successes'] += 1
                    phase_started = time.monotonic()
                    try:
                        candidate = self.intensify(candidate,120)
                    finally:
                        stats[idx]['intensify_seconds'] += time.monotonic()-phase_started
                    m = self.metrics(candidate); archive_gain = False
                    if (m[0],m[1],m[2]) < self.metrics(best_max)[:3]:
                        best_max = [r[:] for r in candidate]; archive_gain = True
                    bv = self.metrics(best_v)
                    if (m[1],m[0],m[2]) < (bv[1],bv[0],bv[2]):
                        best_v = [r[:] for r in candidate]; archive_gain = True
                    if m[0] <= self.limit+1e-9 and (best_feasible is None or m[0]<self.metrics(best_feasible)[0]):
                        best_feasible = [r[:] for r in candidate]; archive_gain = True
                    delta = self.score(candidate)-self.score(current)
                    progress = min(1.,(time.monotonic()-started)/seconds)
                    temp = .15*(.005/.15)**progress
                    accepted = delta<=0 or self.rng.random()<math.exp(-delta/temp)
                    if accepted:
                        current = candidate; stats[idx]['accepted'] += 1
                        reward = 3. if delta<0 else 1.
                    if archive_gain:
                        reward = 8.; stats[idx]['archive_improvements'] += 1
                        history.append({'iteration':it,'seconds':time.monotonic()-started,'Tmax':m[0],'V':m[1],'operator_pair':idx})
                        save()
                weights[idx] = max(.1,.9*weights[idx]+.1*reward)
                if time.monotonic()-last_save>=10:
                    save(); last_save=time.monotonic()
        except BudgetExpired:
            pass
        save()
        return snapshot()


def main(solver_cls=Solver):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--data',default=str(Path(__file__).with_name('instances.json')))
    p.add_argument('--case',default='Case1');p.add_argument('--fleet',type=int,default=3)
    p.add_argument('--seed',type=int,default=0);p.add_argument('--seconds',type=float,default=60)
    p.add_argument('--iterations',type=int,default=1000000)
    p.add_argument('--focus',choices=['max','violation'],default='max')
    p.add_argument('--warm',help='Previous output JSON; preserve all archives (not exact RNG resume)')
    p.add_argument('--out',default='result.json')
    a=p.parse_args()
    if not math.isfinite(a.seconds) or a.seconds<=0 or a.fleet<1 or a.iterations<0: p.error('Invalid budget or fleet')
    instance=json.loads(Path(a.data).read_text())['cases'][a.case]
    s=solver_cls(instance,a.fleet,a.seed,a.focus)
    s.case=a.case
    def stop(signum, frame):
        s.stop_requested = True
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    if a.fleet>s.n:p.error('Fleet exceeds number of task copies')
    warm=None;prior=None
    if a.warm:
        prior=json.loads(Path(a.warm).read_text())
        if prior.get('case')!=a.case or prior['fleet']!=a.fleet or prior.get('instance_sha256')!=s.fingerprint:p.error('Warm-start case/fleet mismatch')
        from validate import validate
        validate({'cases':{a.case:instance}},prior)
        warm=prior['best_violation' if a.focus=='violation' else 'best_makespan']['routes']
    try: result=s.solve(a.seconds,a.iterations,warm,a.out+'.checkpoint.json',archives=prior)
    except BudgetExpired:p.error('Budget expired during initialization; increase --seconds')
    result.update({'case':a.case,'seed':a.seed,'input':str(Path(a.data).resolve()),'prototype':True})
    from validate import validate
    validate({'cases':{a.case:instance}},result)
    atomic_json(a.out,result)
    print(json.dumps({k:result[k] for k in ['case','status','iterations','elapsed_seconds','initial_Tmax']}))
    print('Best Tmax:',result['best_makespan']['Tmax'])


if __name__=='__main__': main()
