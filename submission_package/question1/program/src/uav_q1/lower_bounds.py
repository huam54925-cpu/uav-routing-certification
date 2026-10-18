"""Certified distance lower bounds for repeated visits with nonempty depot tours.
Distances are rounded DOWN to integer micro-km using exact decimal rationals.
Assignment primal/dual certificates are checked with integer arithmetic.
"""
from fractions import Fraction
from math import isqrt

SCALE = 1_000_000

def rational(value):
    return value if isinstance(value,Fraction) else Fraction(str(value))


def distance_matrix(points, unit_km=.1):
    xy=[(Fraction(0),Fraction(0))]+[(rational(p['x']),rational(p['y'])) for p in points]
    factor=rational(unit_km)*SCALE
    result=[]
    for x,y in xy:
        row=[]
        for a,b in xy:
            squared=((x-a)**2+(y-b)**2)*factor**2
            row.append(isqrt(squared.numerator//squared.denominator))
        result.append(row)
    return result


def mst_cost(matrix):
    # Dense Prim includes legitimate zero-length edges, unlike sparse zero-as-absent conventions.
    n=len(matrix);remaining=set(range(1,n));nearest=matrix[0][:];value=0
    while remaining:
        j=min(remaining,key=lambda i:nearest[i]);remaining.remove(j);value+=nearest[j]
        for i in remaining: nearest[i]=min(nearest[i],matrix[j][i])
    return value


def assignment(cost):
    """Square Hungarian method, integer costs and exact optimality verification."""
    n=len(cost);u=[0]*(n+1);v=[0]*(n+1);p=[0]*(n+1);way=[0]*(n+1)
    inf=(max(max(row) for row in cost)+1)*(n+1)*4
    for i in range(1,n+1):
        p[0]=i;j0=0;minimum=[inf]*(n+1);used=[False]*(n+1)
        while True:
            used[j0]=True;i0=p[j0];delta=inf;j1=0
            for j in range(1,n+1):
                if not used[j]:
                    cur=cost[i0-1][j-1]-u[i0]-v[j]
                    if cur<minimum[j]: minimum[j]=cur;way[j]=j0
                    if minimum[j]<delta: delta=minimum[j];j1=j
            for j in range(n+1):
                if used[j]: u[p[j]]+=delta;v[j]-=delta
                else: minimum[j]-=delta
            j0=j1
            if p[j0]==0: break
        while True:
            j1=way[j0];p[j0]=p[j1];j0=j1
            if j0==0: break
    columns=[0]*n
    for j in range(1,n+1): columns[p[j]-1]=j-1
    value=sum(cost[i][columns[i]] for i in range(n))
    cert={'columns':columns,'row_potentials':u[1:],'column_potentials':v[1:],'objective_units':value}
    verify_assignment(cost,cert)
    return cert


def verify_assignment(cost,certificate):
    n=len(cost);cols=certificate['columns'];u=certificate['row_potentials'];v=certificate['column_potentials']
    if sorted(cols)!=list(range(n)) or len(u)!=n or len(v)!=n: raise ValueError('Bad certificate dimensions')
    if any(u[i]+v[j]>cost[i][j] for i in range(n) for j in range(n)): raise ValueError('Dual infeasible')
    primal=sum(cost[i][cols[i]] for i in range(n));dual=sum(u)+sum(v)
    if primal!=dual or primal!=certificate['objective_units']: raise ValueError('Nonzero primal-dual gap')


def assignment_matrix(distances,visits,fleet):
    physical=[i for i,r in enumerate(visits,1) for _ in range(r)]+[0]*fleet
    n=len(physical);penalty=(n+1)*max(max(row) for row in distances)+1
    cost=[[penalty if a==b else distances[a][b] for b in physical] for a in physical]
    return cost,physical,penalty


def fixed_fleet_bound(points,fleet,unit_km=.1,speed_kmh=55,service_minutes=5,limit_h=9,distances=None):
    visits=[int(p['visits']) for p in points]
    if not points or any(r<=0 for r in visits) or not 1<=fleet<=sum(visits): raise ValueError('Invalid visits/fleet')
    d=distance_matrix(points,unit_km) if distances is None else distances
    cost,physical,penalty=assignment_matrix(d,visits,fleet)
    cert=assignment(cost)
    if any(cost[i][j]==penalty for i,j in enumerate(cert['columns'])):
        return {'fleet':fleet,'excluded':True,'reason':'no allowed cycle cover','certificate':cert}
    mst=mst_cost(d)
    # Every task occurrence has TWO incidences, possibly to the same neighbor.
    task_degree=sum(r*min(d[i][j] for j in range(len(d)) if j!=i) for i,r in enumerate(visits,1))
    depot_degree=fleet*min(d[0][1:])
    routing=max(mst,task_degree+depot_degree,cert['objective_units'])
    speed=rational(speed_kmh);service=rational(service_minutes)/60
    if speed<=0 or service<0 or rational(limit_h)<=0: raise ValueError('Invalid model parameters')
    aggregate=sum(visits)*service+Fraction(routing,SCALE)/speed
    farthest=max(2*Fraction(x,SCALE)/speed+service for x in d[0][1:])
    lower=max(aggregate/fleet,farthest)
    cycles=[];unseen=set(range(len(physical)))
    while unseen:
        start=min(unseen);cycle=[];current=start
        while current in unseen:
            unseen.remove(current);cycle.append(current);current=cert['columns'][current]
        cycles.append({'size':len(cycle),'depot_copies':sum(physical[i]==0 for i in cycle)})
    return {'fleet':fleet,'excluded':lower>rational(limit_h),'mst_km':mst/SCALE,
            'repeat_degree_km':task_degree/SCALE,'depot_degree_km':depot_degree/SCALE,
            'cycle_cover_km':cert['objective_units']/SCALE,'routing_lower_km':routing/SCALE,
            'aggregate_work_hours':float(aggregate),'makespan_lower_bound_h':float(lower),
            'makespan_lower_bound_fraction':str(lower),'farthest_roundtrip_h':float(farthest),
            'service_hours':float(sum(visits)*service),'cycles':cycles,'certificate':cert}


def minimum_fleet_bound(points,**parameters):
    d=distance_matrix(points,parameters.get('unit_km',.1))
    speed=rational(parameters.get('speed_kmh',55));service=rational(parameters.get('service_minutes',5))/60
    limit=rational(parameters.get('limit_h',9))
    if max(2*Fraction(x,SCALE)/speed+service for x in d[0][1:])>limit:
        raise ValueError('Even a single required depot roundtrip exceeds the deadline')
    checks=[]
    for fleet in range(1,sum(int(p['visits']) for p in points)+1):
        bound=fixed_fleet_bound(points,fleet,distances=d,**parameters);checks.append(bound)
        if not bound['excluded']: return fleet,checks
    raise ValueError('All fleet counts excluded by necessary conditions')
