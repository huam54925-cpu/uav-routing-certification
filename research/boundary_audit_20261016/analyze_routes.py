"""Bounded structural diagnostics and one-copy relocations, not a long search."""
import argparse
from collections import Counter,defaultdict
import hashlib
import json
import math
from pathlib import Path
import zipfile

ROOT=Path(__file__).resolve().parents[2]

def read_snapshot(path):
    with zipfile.ZipFile(path) as z:
        name=next(n for n in z.namelist() if n.endswith('/best.json'))
        return json.loads(z.read(name))

def analyze(ins,record):
    copies=[p for p in ins['points'] for _ in range(p['visits'])]
    physical=[p['id'] for p in copies];points={p['id']:p for p in ins['points']}
    xy={0:(0.,0.),**{p['id']:(p['x'],p['y']) for p in ins['points']}}
    def dist(a,b):return math.dist(xy[a],xy[b])*ins['unit_km']
    def valid(r):return bool(r) and all(physical[a]!=physical[b] for a,b in zip(r,r[1:]))
    def route_time(r):
        seq=[0]+[physical[u] for u in r]+[0]
        return sum(dist(a,b) for a,b in zip(seq,seq[1:]))/ins['speed_kmh']+len(r)*ins['service_h']
    def metrics(rs):
        ts=[route_time(r) for r in rs]
        return {'Tmax':max(ts),'violation_h':sum(max(0,t-9) for t in ts),'total_h':sum(ts),'times_h':ts}
    rs=record['best_makespan']['routes'];original=metrics(rs)
    fingerprint=hashlib.sha256(json.dumps(ins,sort_keys=True).encode()).hexdigest()
    if record.get('instance_sha256')!=fingerprint:raise ValueError('Instance hash mismatch')
    if len(rs)!=record['fleet']:raise ValueError('Fleet mismatch')
    if Counter(u for r in rs for u in r)!=Counter(range(len(copies))) or not all(valid(r) for r in rs):raise ValueError('Bad routes')
    if any(abs(original[k]-record['best_makespan'][k])>1e-8 for k in ('Tmax','violation_h','total_h')):raise ValueError('Bad metrics')
    edges=[];edge_owners=defaultdict(list);excursions=[];owners=defaultdict(list)
    for k,r in enumerate(rs):
        ids=[physical[u] for u in r];seq=[0]+ids+[0]
        for i,(a,b) in enumerate(zip(seq,seq[1:])):
            edges.append({'uav':k+1,'from':a,'to':b,'km':dist(a,b),'depot_edge':0 in (a,b)})
            edge_owners[tuple(sorted((a,b)))].append(k+1)
        positions=defaultdict(list)
        for i,p in enumerate(ids):positions[p].append(i);owners[p].append(k+1)
        for point,indices in positions.items():
            for a,b in zip(indices,indices[1:]):
                segment=ids[a:b+1]
                excursions.append({'uav':k+1,'point':point,'segment':segment,
                    'flight_km':sum(dist(x,y) for x,y in zip(segment,segment[1:])),
                    'intermediate_visits':b-a-1})
    moves=[];seam_rejections=0;adjacency_rejections=0
    for a,r in enumerate(rs):
        count=Counter(physical[u] for u in r)
        for i,u in enumerate(r):
            point=physical[u]
            if count[point]<2:continue
            reduced=r[:i]+r[i+1:]
            if not valid(reduced):seam_rejections+=1;continue
            source_before=physical[r[i-1]] if i else 0
            source_after=physical[r[i+1]] if i+1<len(r) else 0
            removed_km=dist(source_before,point)+dist(point,source_after)-dist(source_before,source_after)
            for b,target in enumerate(rs):
                if a==b or point in [physical[v] for v in target]:continue
                for j in range(len(target)+1):
                    inserted=target[:j]+[u]+target[j:]
                    if not valid(inserted):adjacency_rejections+=1;continue
                    left=physical[target[j-1]] if j else 0
                    right=physical[target[j]] if j<len(target) else 0
                    added_km=dist(left,point)+dist(point,right)-dist(left,right)
                    candidate=[x[:] for x in rs];candidate[a]=reduced;candidate[b]=inserted
                    m=metrics(candidate)
                    moves.append({'point':point,'task_copy':u,'source_uav':a+1,'destination_uav':b+1,
                        'source_context':[source_before,point,source_after],
                        'destination_edge':[left,right], 'destination_position':j,
                        'source_removed_km':removed_km,'destination_added_km':added_km,
                        'total_flight_saved_km':removed_km-added_km,
                        'source_time_change_h':-removed_km/ins['speed_kmh']-ins['service_h'],
                        'destination_time_change_h':added_km/ins['speed_kmh']+ins['service_h'],
                        'new_metrics':m})
    swaps=[]
    for a in range(len(rs)):
        for b in range(a+1,len(rs)):
            ca=Counter(physical[u] for u in rs[a]);cb=Counter(physical[u] for u in rs[b])
            for i,u in enumerate(rs[a]):
                for j,v in enumerate(rs[b]):
                    if physical[u]==physical[v] or (ca[physical[u]]<2 and cb[physical[v]]<2):continue
                    ra=rs[a][:];rb=rs[b][:];ra[i]=v;rb[j]=u
                    if not valid(ra) or not valid(rb):continue
                    candidate=[r[:] for r in rs];candidate[a]=ra;candidate[b]=rb
                    m=metrics(candidate)
                    swaps.append({'uavs':[a+1,b+1],'points':[physical[u],physical[v]],
                        'positions':[i,j],'task_copies':[u,v],'new_metrics':m,
                        'total_flight_saved_km':(original['total_h']-m['total_h'])*ins['speed_kmh']})
    shared=[{'edge' :list(edge),'uavs':sorted(set(v)),'traversals':len(v),'km':dist(*edge)}
            for edge,v in edge_owners.items() if len(set(v))>1]
    def key(move):
        m=move['new_metrics'];return (m['Tmax'],m['violation_h'],m['total_h'])
    return {'case':record['case'],'archive':'best_makespan','original':original,
            'repeated_point_owners':{str(p):v for p,v in owners.items() if len(v)>1},
            'longest_edges':sorted(edges,key=lambda e:e['km'],reverse=True)[:12],
            'shared_exact_undirected_edges':sorted(shared,key=lambda e:e['km'],reverse=True),
            'longest_revisit_segments':sorted(excursions,key=lambda e:e['flight_km'],reverse=True)[:8],
            'relocation_scope':'one copy from same-UAV repeated point to UAV with no existing visit to that point; all insertion positions',
            'swap_legal_candidates':len(swaps),
            'swap_strict_Tmax_improving':sum(m['new_metrics']['Tmax']<original['Tmax']-1e-10 for m in swaps),
            'best_swaps':sorted(swaps,key=key)[:5],
            'legal_candidates':len(moves),'source_seam_rejections':seam_rejections,'destination_rejections':adjacency_rejections,
            'strict_Tmax_improving_moves':sum(m['new_metrics']['Tmax']<original['Tmax']-1e-10 for m in moves),
            'positive_total_distance_moves':sum(m['total_flight_saved_km']>1e-10 for m in moves),
            'best_Tmax_moves':sorted(moves,key=key)[:5],
            'largest_distance_saving_moves':sorted(moves,key=lambda m:-m['total_flight_saved_km'])[:5]}

def main():
    p=argparse.ArgumentParser();p.add_argument('--case1-zip',required=True);p.add_argument('--case3-zip',required=True);p.add_argument('--out',required=True)
    a=p.parse_args();data=json.loads((ROOT/'research/alns_next/instances.json').read_text());report={}
    for case,path in [('Case1',a.case1_zip),('Case3',a.case3_zip)]:
        record=read_snapshot(path)
        if record['case']!=case:raise ValueError('Wrong case')
        result=analyze(data['cases'][case],record)
        result['input_zip_sha256']=hashlib.sha256(Path(path).read_bytes()).hexdigest();report[case]=result
    Path(a.out).write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    for c,r in report.items():
        print(c,'legal relocations',r['legal_candidates'],'Tmax improving',r['strict_Tmax_improving_moves'],'distance improving',r['positive_total_distance_moves'])
        print('best Tmax',r['best_Tmax_moves'][0]);print('best total-distance saving',r['largest_distance_saving_moves'][0]);print('long revisit',r['longest_revisit_segments'][:2]);print('swaps',r['swap_legal_candidates'],r['swap_strict_Tmax_improving'],r['best_swaps'][:1])

if __name__=='__main__':main()
