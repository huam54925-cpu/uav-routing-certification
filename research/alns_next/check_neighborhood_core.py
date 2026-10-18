"""Tiny exhaustive reference plus invariants; no third-party dependencies."""
from collections import Counter
from itertools import permutations
import json
import math
from alns_solver import BudgetExpired
from neighborhood_core import EnhancedSolver


def instance():
    return dict(unit_km=.1, speed_kmh=55, service_h=5/60, limit_h=9,
                points=[dict(id=1,x=10,y=0,visits=2),
                        dict(id=2,x=0,y=10,visits=2),
                        dict(id=3,x=20,y=20,visits=1)])


def independent_times(s, routes):
    copies=[p for p in s.data['points'] for _ in range(p['visits'])]
    ts=[]
    for r in routes:
        points=[(0,0)]+[(copies[u]['x'],copies[u]['y']) for u in r]+[(0,0)]
        ts.append(sum(math.dist(a,b) for a,b in zip(points,points[1:]))*.1/55+len(r)*5/60)
    return ts


def check(s, routes):
    assert len(routes)==s.k and all(routes)
    assert Counter(u for r in routes for u in r)==Counter(range(s.n))
    assert all(s.valid(r) for r in routes)
    assert all(abs(a-b)<1e-12 for a,b in zip(independent_times(s,routes),s.metrics(routes)[3]))


def main():
    # Exhaustively enumerate every task-copy order and every two-route split.
    s=EnhancedSolver(instance(),2)
    exact=float('inf'); feasible=[]
    for perm in permutations(range(s.n)):
        for cut in range(1,s.n):
            routes=[list(perm[:cut]),list(perm[cut:])]
            if all(s.valid(r) for r in routes):
                feasible.append(routes)
                exact=min(exact,max(independent_times(s,routes)))
    feasible=[r for r in feasible if max(independent_times(s,r)) > exact+1e-10]
    assert feasible
    best=float('inf'); repairs=0; improvements=0
    for seed in range(30):
        s=EnhancedSolver(instance(),2,seed)
        routes=feasible[seed % len(feasible)]
        before=[r[:] for r in routes]
        improved=s.cross_exchange(routes,200)
        check(s,improved)
        assert routes==before
        assert s.score(improved)<=s.score(routes)+1e-12
        if s.metrics(improved)[0] < s.metrics(routes)[0]-1e-12:
            improvements += 1
        best=min(best,s.metrics(improved)[0])
        for _ in range(10):
            partial,removed=s.destroy(routes,4)
            assert Counter([u for r in partial for u in r]+removed)==Counter(range(s.n))
            assert all(s.valid(r) for r in partial)
            repaired=s.repair(partial,removed,1)
            if repaired is not None:
                check(s,repaired); repairs+=1
    assert best>=exact-1e-12
    assert improvements > 0
    assert abs(best-exact)<1e-12
    assert s.diagnostics['joint_calls']==10
    s.deadline=0
    try:
        s.cross_exchange(routes)
    except BudgetExpired:
        pass
    else:
        raise AssertionError('Deadline ignored')
    print(json.dumps(dict(status='PASS',seeds=30,nonoptimal_starts=30,strict_Tmax_improvements=improvements,repair_checks=repairs,
                          exact_tiny_Tmax=exact,observed_best_Tmax=best,
                          gap=best-exact,scope='5 task copies, 2 UAVs; not full-case performance'),indent=2))


if __name__=='__main__':
    main()
