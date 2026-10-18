"""Serial, paired wall-clock ablation; same warm archive for every run."""
import argparse
import hashlib
import json
import math
from pathlib import Path
import subprocess
import sys
from alns_solver import atomic_json
from validate import validate

HERE=Path(__file__).resolve().parent

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--warm',required=True)
    p.add_argument('--out',required=True,help='Must be a NEW directory')
    p.add_argument('--seconds',type=float,default=600)
    p.add_argument('--seeds',type=int,nargs='+',default=[0,1,2])
    a=p.parse_args()
    if not math.isfinite(a.seconds) or a.seconds<=0:
        p.error('seconds must be finite and positive')
    data=json.loads((HERE/'instances.json').read_text())
    warm=json.loads(Path(a.warm).read_text());validate(data,warm)
    out=Path(a.out).resolve();out.mkdir(parents=True,exist_ok=False)
    atomic_json(out/'warm.json',warm)
    sources={name:hashlib.sha256((HERE/name).read_bytes()).hexdigest()
             for name in ('alns_solver.py','neighborhood_core.py','run_variant.py','validate.py','instances.json','run_ablation.py')}
    variants=['baseline','joint','cross','both']
    atomic_json(out/'experiment.json',{'seconds_per_run':a.seconds,'seeds':a.seeds,
        'variants':variants,'source_hashes':sources,'checkpoint_io':True,
        'order':'cyclic rotation by seed index; not statistically independent trials',
        'cross_budget':'half original intensification proposals replaced by cross exchange'})
    summary=[]
    for index,seed in enumerate(a.seeds):
        order=variants[index%4:]+variants[:index%4]
        for variant in order:
            stem=f'{index:02d}_{variant}_seed{seed}';result_path=out/(stem+'.json')
            command=[sys.executable,str(HERE/'run_variant.py'),'--variant',variant,
                '--case',warm['case'],'--fleet',str(warm['fleet']),'--seed',str(seed),
                '--seconds',str(a.seconds),'--iterations','1000000000000',
                '--focus','max','--warm',str(out/'warm.json'),'--out',str(result_path)]
            print('Starting',stem,flush=True)
            with (out/(stem+'.log')).open('w') as log:
                try:
                    proc=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,timeout=a.seconds+120)
                    row={'variant':variant,'seed':seed,'returncode':proc.returncode}
                except subprocess.TimeoutExpired:
                    row={'variant':variant,'seed':seed,'error':'process timeout'}
            if row.get('returncode')==0:
                result=json.loads(result_path.read_text());validate(data,result)
                row.update(Tmax=result['best_makespan']['Tmax'],
                    violation=result['best_violation']['violation_h'],
                    iterations=result['iterations'],elapsed_seconds=result['elapsed_seconds'],
                    status=result['status'],validated=True)
            summary.append(row);atomic_json(out/'summary.json',summary)
            print(json.dumps(row),flush=True)

if __name__=='__main__':
    main()
