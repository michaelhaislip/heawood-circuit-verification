"""Repeat the six-cycle comparisons with normalization disabled."""
import argparse,json,pathlib,random,subprocess,sys
from intermediate_benchmark import CASES
from circuit_benchmark import solve

def main():
    p=argparse.ArgumentParser();p.add_argument('--worker',action='store_true')
    p.add_argument('--size',type=int);p.add_argument('--encoding');p.add_argument('--seed',type=int)
    p.add_argument('--output',default='normalization-ablation.jsonl');a=p.parse_args()
    if a.worker:
        n,edges=CASES['cycle6']
        r=solve(n,edges,a.size,5,a.encoding,False,seed=a.seed)
        r['case']='cycle6';print(json.dumps(r),flush=True);return
    jobs=[(size,seed,enc) for size in [7,8] for seed in [0,1,2] for enc in ['ite','implication']]
    random.Random(20261124).shuffle(jobs)
    with pathlib.Path(a.output).open('w',encoding='utf-8') as f:
        for i,(size,seed,enc) in enumerate(jobs):
            proc=subprocess.run([sys.executable,str(pathlib.Path(__file__).resolve()),'--worker',
                 '--size',str(size),'--seed',str(seed),'--encoding',enc],capture_output=True,text=True,timeout=65)
            if proc.returncode:raise RuntimeError(proc.stderr)
            r=json.loads(proc.stdout);r['order']=i
            if size==8:assert r['result']!='unsat'
            f.write(json.dumps(r)+'\n');f.flush()
            print(f"{i+1}/12 unnormalized cycle6 size={size} seed={seed} {enc}: {r['result']} ({r['check_seconds']:.3f}s)",flush=True)
if __name__=='__main__':main()
