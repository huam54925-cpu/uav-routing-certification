"""Physical-node directed LP with connectivity cuts and exact dual bound repair.
No LP numerical objective or numerical infeasibility is used as a proof.
"""
import argparse
import hashlib
from fractions import Fraction as F
import json
from pathlib import Path
import signal
import sys
import time
import warnings
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix,csr_matrix
from alns_solver import atomic_json
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'submission_package/question1/program/src'))
from uav_q1.lower_bounds import distance_matrix,SCALE

def mincut(cap,source,sink,deadline):
    n=len(cap);res=cap.copy()
    while True:
        if time.monotonic()>=deadline:raise TimeoutError
        parent=[-1]*n;parent[source]=source;q=[source]
        for u in q:
            for v in np.flatnonzero(res[u]>1e-8):
                if parent[v]<0:parent[v]=u;q.append(int(v))
            if parent[sink]>=0:break
        if parent[sink]<0:return frozenset(q)
        v=sink;flow=float('inf')
        while v!=source:u=parent[v];flow=min(flow,res[u,v]);v=u
        v=sink
        while v!=source:u=parent[v];res[u,v]-=flow;res[v,u]+=flow;v=u

def repaired_certificate(cost,arcs,upper,degree,cuts,eqdual,cutdual):
    # Equality duals are free; Ax<=b duals must be <=0. Repair residuals with finite upper bounds.
    y=[F.from_float(float(x)) for x in eqdual]
    z=[min(F(0),F.from_float(float(x))) for x in cutdual]
    n=len(degree);value=sum(F(d)*(y[i]+y[n+i]) for i,d in enumerate(degree))-sum(z)
    penalty=F(0)
    for k,(a,b) in enumerate(arcs):
        reduced=F(int(cost[k]))-y[a]-y[n+b]
        for subset,multiplier in zip(cuts,z):
            if a in subset and b not in subset:reduced+=multiplier
        penalty+=min(F(0),reduced)*int(upper[k])
    value+=penalty
    return {'distance_units_fraction':str(value),'eq_dual':[str(v) for v in y],
            'cut_dual':[str(v) for v in z],'residual_correction_units':str(penalty)}

def build(ins,fleet):
    if ins['service_h']!=5/60:raise ValueError('Expected five minute service')
    d=distance_matrix(ins['points'],ins['unit_km']);degree=[fleet]+[p['visits'] for p in ins['points']]
    n=len(d);arcs=[(a,b) for a in range(n) for b in range(n) if a!=b]
    cost=np.array([d[a][b] for a,b in arcs],dtype=np.int64)
    upper=np.array([min(degree[a],degree[b]) for a,b in arcs])
    rows=[];cols=[]
    for k,(a,b) in enumerate(arcs):rows.extend([a,n+b]);cols.extend([k,k])
    eq=coo_matrix((np.ones(len(rows)),(rows,cols)),shape=(2*n,len(arcs))).tocsr()
    return degree,arcs,cost,upper,eq

def solve(ins,fleet,seconds,out,max_rounds=100):
    started=time.monotonic();deadline=started+seconds;stop=False
    def halt(*_):
        nonlocal stop
        stop=True
    signal.signal(signal.SIGTERM,halt);signal.signal(signal.SIGINT,halt)
    degree,arcs,cost,upper,eq=build(ins,fleet);n=len(degree);cuts=[];seen=set();best=F(0)
    record={'instance_sha256':hashlib.sha256(json.dumps(ins,sort_keys=True).encode()).hexdigest(),'status':'RUNNING','fleet':fleet,'rounds':[],'certificate':None,'Tmax_lower_h':0,'excluded_9h':False}
    def save():
        record['elapsed_seconds']=time.monotonic()-started;atomic_json(out,record)
    save()
    try:
        for iteration in range(max_rounds):
            if stop or time.monotonic()>=deadline:break
            row=[];col=[]
            for i,s in enumerate(cuts):
                for k,(a,b) in enumerate(arcs):
                    if a in s and b not in s:row.append(i);col.append(k)
            ub=coo_matrix((-np.ones(len(row)),(row,col)),shape=(len(cuts),len(arcs))).tocsr() if cuts else None
            with warnings.catch_warnings():
                warnings.filterwarnings('ignore',message='Unrecognized options detected')
                r=linprog(cost,A_ub=ub,b_ub=-np.ones(len(cuts)) if cuts else None,
                          A_eq=eq,b_eq=degree*2,bounds=np.column_stack([np.zeros(len(arcs)),upper]),
                          method='highs',options={'threads':1,'time_limit':max(.01,min(60,deadline-time.monotonic()))})
            if not r.success:
                record['solver_message']=r.message;break
            cert=repaired_certificate(cost,arcs,upper,degree,cuts,r.eqlin.marginals,r.ineqlin.marginals)
            value=F(cert['distance_units_fraction'])
            if value>=best:
                best=value;record['certificate']={**cert,'cuts':[sorted(s) for s in cuts]}
                total=F(sum(degree[1:]),12)+best/SCALE/F(str(ins['speed_kmh']))
                lower=total/fleet;record['Tmax_lower_h']=float(lower);record['Tmax_lower_fraction']=str(lower)
                record['excluded_9h']=lower>F(str(ins['limit_h']))
            record['rounds'].append({'iteration':iteration,'cuts':len(cuts),'lp_distance_km':float(r.fun/SCALE),
                                     'certified_Tmax_lower_h':record['Tmax_lower_h']});save()
            if record['excluded_9h']:break
            cap=np.zeros((n,n))
            for (a,b),x in zip(arcs,r.x):cap[a,b]=max(0,float(x))
            new=[]
            for source in range(1,n):
                if stop:break
                subset=mincut(cap,source,0,deadline)
                crossing=sum(cap[a,b] for a in subset for b in range(n) if b not in subset)
                if crossing<1-1e-7 and subset not in seen:
                    seen.add(subset);new.append(subset)
            if not new:
                record['termination']='no_new_connectivity_cut';break
            cuts.extend(new)
    except TimeoutError:record['termination']='budget'
    finally:
        record['status']='BOUND_ONLY';save()
    return record

def verify(ins,fleet,record):
    cert=record['certificate']
    if cert is None:return False
    degree,arcs,cost,upper,_=build(ins,fleet);cuts=[frozenset(s) for s in cert['cuts']]
    if any(not s or 0 in s or not s<=set(range(1,len(degree))) for s in cuts):raise ValueError('Invalid connectivity cut')
    y=list(map(F,cert['eq_dual']));z=list(map(F,cert['cut_dual']))
    if len(y)!=2*len(degree) or len(z)!=len(cuts) or any(v>0 for v in z):raise ValueError('Invalid dual')
    # Re-evaluate exact serialized fractions without converting them to float.
    value=sum(F(d)*(y[i]+y[len(degree)+i]) for i,d in enumerate(degree))-sum(z)
    for k,(a,b) in enumerate(arcs):
        rc=F(int(cost[k]))-y[a]-y[len(degree)+b]+sum(z[j] for j,s in enumerate(cuts) if a in s and b not in s)
        value+=min(F(0),rc)*int(upper[k])
    if value!=F(cert['distance_units_fraction']):raise ValueError('Certificate objective mismatch')
    lower=(F(sum(degree[1:]),12)+value/SCALE/F(str(ins['speed_kmh'])))/fleet
    if str(lower)!=record['Tmax_lower_fraction'] or (lower>F(str(ins['limit_h'])))!=record['excluded_9h']:raise ValueError('Bound claim mismatch')
    return True

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--case',required=True);p.add_argument('--fleet',type=int,required=True)
    p.add_argument('--seconds',type=float,default=600);p.add_argument('--out',required=True);p.add_argument('--verify',action='store_true')
    a=p.parse_args();ins=json.loads(Path(__file__).with_name('instances.json').read_text())['cases'][a.case]
    if a.verify:
        if not verify(ins,a.fleet,json.loads(Path(a.out).read_text())):raise ValueError('No certificate')
        print('Certificate PASS')
    else:
        result=solve(ins,a.fleet,a.seconds,a.out)
        if result['certificate'] is not None:assert verify(ins,a.fleet,result)
        print(result['Tmax_lower_h'],result['excluded_9h'])
