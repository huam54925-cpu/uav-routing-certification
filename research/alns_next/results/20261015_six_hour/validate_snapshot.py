"""Independent validator: recompute from coordinates, never import solver."""
import argparse
from collections import Counter
import json
import math
import hashlib
from pathlib import Path


def validate(data, result):
    ins = data['cases'][result['case']]
    fingerprint=hashlib.sha256(json.dumps(ins,sort_keys=True).encode()).hexdigest()
    if result.get('instance_sha256')!=fingerprint:raise ValueError('Instance hash mismatch')
    if result.get('status') not in ('FEASIBLE','UNKNOWN'):raise ValueError('Invalid heuristic status')
    if type(result.get('fleet')) is not int or result['fleet']<1:raise ValueError('Invalid fleet')
    if any(result.get(k) is None for k in ('best_makespan','best_violation')):raise ValueError('Missing required archive')
    copies = []
    for p in ins['points']:
        copies.extend([p]*p['visits'])
    reports = {}
    for key in ['best_makespan','best_violation','best_feasible']:
        item=result.get(key)
        if item is None:
            reports[key]=None;continue
        routes=item['routes'];times=[]
        if len(routes)!=result['fleet']:raise ValueError('Fleet mismatch')
        flat=[u for r in routes for u in r]
        if any(type(u) is not int for u in flat):raise ValueError('Task ID is not integer')
        if Counter(flat)!=Counter(range(len(copies))):raise ValueError('Missing/duplicated task copy')
        for route in routes:
            if not route:raise ValueError('Empty route')
            pts=[copies[u] for u in route]
            if any(a['id']==b['id'] for a,b in zip(pts,pts[1:])):raise ValueError('Consecutive same physical point')
            coords=[(0,0)]+[(p['x'],p['y']) for p in pts]+[(0,0)]
            distance=sum(math.hypot(a[0]-b[0],a[1]-b[1]) for a,b in zip(coords,coords[1:]))*ins['unit_km']
            times.append(distance/ins['speed_kmh']+len(route)*ins['service_h'])
        t=max(times);v=sum(max(0,t-ins['limit_h']) for t in times)
        for name,actual in [('Tmax',t),('violation_h',v),('total_h',sum(times))]:
            if not math.isfinite(item[name]) or abs(item[name]-actual)>1e-8:raise ValueError('Metric mismatch: '+name)
        if len(item['times_h'])!=len(times) or any(not math.isfinite(x) or abs(x-y)>1e-8 for x,y in zip(item['times_h'],times)):raise ValueError('Route times mismatch')
        feasible=t<=ins['limit_h']+1e-9
        if key=='best_feasible' and not feasible:raise ValueError('False feasible claim')
        reports[key]={'structurally_valid':True,'feasible_9h':feasible,'Tmax':t,'violation_h':v,'times_h':times}
    if result['status']=='FEASIBLE' and result.get('best_feasible') is None:raise ValueError('Missing feasible witness')
    if result['status']=='UNKNOWN' and any(x and x['feasible_9h'] for x in reports.values()):raise ValueError('Feasible archive has UNKNOWN status')
    return reports


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('result');p.add_argument('--data',default=str(Path(__file__).with_name('instances.json')))
    a=p.parse_args();print(json.dumps(validate(json.loads(Path(a.data).read_text()),json.loads(Path(a.result).read_text())),indent=2))
