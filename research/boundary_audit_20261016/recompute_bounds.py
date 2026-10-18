"""Recompute safe lower bounds or independently check stored assignment witnesses."""
import argparse
import hashlib
import json
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'submission_package/question1/program/src'))
from uav_q1.lower_bounds import minimum_fleet_bound, distance_matrix, assignment_matrix, verify_assignment

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--verify',action='store_true');parser.add_argument('--out',default=str(Path(__file__).with_name('lower_bound_certificates.json')))
    args=parser.parse_args();data_path=ROOT/'research/alns_next/instances.json';data=json.loads(data_path.read_text())
    if args.verify:
        records=json.loads(Path(args.out).read_text())
        for case,record in records.items():
            ins=data['cases'][case];d=distance_matrix(ins['points']);visits=[p['visits'] for p in ins['points']]
            for item in record['checks']:
                cost,_,_=assignment_matrix(d,visits,item['fleet']);verify_assignment(cost,item['certificate'])
            print(case,'integer assignment primal/dual certificates PASS')
    else:
        records={}
        for case,ins in data['cases'].items():
            n,checks=minimum_fleet_bound(ins['points']);records[case]={'N_lower':n,'checks':checks}
            print(case,n)
        Path(args.out).write_text(json.dumps(records,indent=2)+'\n')
    print('instances.json SHA256',hashlib.sha256(data_path.read_bytes()).hexdigest())
if __name__=='__main__':main()
