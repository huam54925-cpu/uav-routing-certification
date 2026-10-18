"""Standard-library-only independent verification; imports neither LP solver nor bound generator."""
from fractions import Fraction as Q
from math import isqrt
import hashlib
import json
from pathlib import Path

def verify(ins,fleet,record):
    if record.get('certificate') is None:return False
    fingerprint=hashlib.sha256(json.dumps(ins,sort_keys=True).encode()).hexdigest()
    if record.get('instance_sha256')!=fingerprint or record['fleet']!=fleet:raise ValueError('Bound identity mismatch')
    if ins['service_h']!=5/60:raise ValueError('This certificate model uses 5 minute visits')
    points=[(Q(0),Q(0))]+[(Q(str(p['x'])),Q(str(p['y']))) for p in ins['points']]
    deg=[fleet]+[p['visits'] for p in ins['points']];n=len(deg)
    cert=record['certificate'];y=list(map(Q,cert['eq_dual']));z=list(map(Q,cert['cut_dual']))
    sets=[set(s) for s in cert['cuts']]
    if len(y)!=2*n or len(z)!=len(sets) or any(v>0 for v in z):raise ValueError('Bad dual dimensions/sign')
    if any(not s or 0 in s or not s<=set(range(1,n)) for s in sets):raise ValueError('Invalid cut subset')
    bound=sum(Q(d)*(y[i]+y[n+i]) for i,d in enumerate(deg))-sum(z)
    factor=Q(str(ins['unit_km']))*1000000
    for i,(x,ycoord) in enumerate(points):
        for j,(a,b) in enumerate(points):
            if i==j:continue
            sq=((x-a)**2+(ycoord-b)**2)*factor**2
            cost=isqrt(sq.numerator//sq.denominator)
            residual=Q(cost)-y[i]-y[n+j]
            residual+=sum(mult for subset,mult in zip(sets,z) if i in subset and j not in subset)
            bound+=min(Q(0),residual)*min(deg[i],deg[j])
    if bound!=Q(cert['distance_units_fraction']):raise ValueError('Distance witness mismatch')
    lower=(Q(sum(deg[1:]),12)+bound/1000000/Q(str(ins['speed_kmh'])))/fleet
    if lower!=Q(record['Tmax_lower_fraction']):raise ValueError('Time witness mismatch')
    if record['excluded_9h']!=(lower>Q(str(ins['limit_h']))):raise ValueError('False exclusion flag')
    return True

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('record');p.add_argument('--case',required=True);p.add_argument('--fleet',type=int,required=True)
    a=p.parse_args();ins=json.loads(Path(__file__).with_name('instances.json').read_text())['cases'][a.case]
    if not verify(ins,a.fleet,json.loads(Path(a.record).read_text())):raise ValueError('No certificate')
    print('Independent exact-rational certificate PASS')
