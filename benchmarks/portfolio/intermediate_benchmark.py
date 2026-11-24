"""Fresh-process, interleaved multi-seed search benchmark; no proof certificates."""
import argparse, itertools, json, os, pathlib, platform, random, subprocess, sys
import z3
from circuit_benchmark import solve, truth

CASES={
 'matching3':(6,[(0,1),(2,3),(4,5)]),
 'cycle5':(5,[(i,(i+1)%5) for i in range(5)]),
 'cycle6':(6,[(i,(i+1)%6) for i in range(6)]),
 'cycle7':(7,[(i,(i+1)%7) for i in range(7)]),
}

def upper_witness(n,edges):
    cover=next(c for k in range(n+1) for c in itertools.combinations(range(n),k)
               if all(a in c or b in c for a,b in edges))
    remaining=list(edges); gates=[]; outputs=[]
    def gate(op,a,b):
        gates.append([op,a,b]); return n+1+len(gates)
    for c in cover:
        assigned=[e for e in remaining if c in e]
        remaining=[e for e in remaining if c not in e]
        if not assigned: continue
        ns=[b if a==c else a for a,b in assigned]; v=ns[0]
        for w in ns[1:]: v=gate(1,v,w)
        outputs.append(gate(0,c,v))
    out=outputs[0]
    for v in outputs[1:]: out=gate(1,out,v)
    for mask in range(1<<n):
        values=[bool(mask>>i&1) for i in range(n)]+[False,True]
        for op,a,b in gates: values.append(values[a]&values[b] if op==0 else values[a]|values[b])
        assert values[out]==bool(truth(n,edges,mask))
    return {'cover':cover,'gates':gates,'output':out,'size':len(gates),'full_table_checked':1<<n}

def main():
    p=argparse.ArgumentParser();p.add_argument('--worker',action='store_true')
    p.add_argument('--case',choices=CASES);p.add_argument('--size',type=int)
    p.add_argument('--encoding',choices=['ite','implication']);p.add_argument('--seed',type=int)
    p.add_argument('--timeout',type=int,default=5);p.add_argument('--output',default='intermediate-results.jsonl')
    a=p.parse_args()
    if a.worker:
        n,edges=CASES[a.case]
        r=solve(n,edges,a.size,a.timeout,a.encoding,True,seed=a.seed)
        r['case']=a.case;print(json.dumps(r),flush=True);return
    jobs=[]; oracles={}
    for name,(n,edges) in CASES.items():
        upper=upper_witness(n,edges);oracles[name]=upper
        for size in [upper['size']-1,upper['size']]:
            for seed in [0,1,2]:
                for encoding in ['ite','implication']:jobs.append((name,size,seed,encoding))
    random.Random(20261123).shuffle(jobs)
    with pathlib.Path(a.output).open('w',encoding='utf-8') as f:
        def emit(r):f.write(json.dumps(r)+'\n');f.flush()
        emit({'environment':{'python':platform.python_version(),'z3':z3.get_version_string(),
          'platform':platform.system(),'processor':platform.machine()},
          'schedule_seed':20261123,'seeds':[0,1,2],'timeout_s':a.timeout,
          'fresh_process_per_run':True,'normalization':True,'upper_witnesses':oracles,
          'independent_minimum':'matching3=5 by essential-input bound (6 inputs require >=5 binary gates); no independent minima claimed for cycles'})
        for i,(name,size,seed,encoding) in enumerate(jobs):
            cmd=[sys.executable,str(pathlib.Path(__file__).resolve()),'--worker','--case',name,
                 '--size',str(size),'--seed',str(seed),'--encoding',encoding,'--timeout',str(a.timeout)]
            proc=subprocess.run(cmd,text=True,capture_output=True,timeout=a.timeout+60)
            if proc.returncode:raise RuntimeError(proc.stderr)
            r=json.loads(proc.stdout);r['order']=i
            if size==oracles[name]['size']:r['expected']='sat (independently verified upper witness)'
            else:r['expected']='unsat (essential-input bound)' if name=='matching3' else 'not independently established'
            if name=='matching3' and r['result']!='unknown':
                assert r['result']==('sat' if size==5 else 'unsat')
            if size==oracles[name]['size']:assert r['result']!='unsat',r
            emit(r)
            print(f"{i+1}/{len(jobs)} {name} size={size} seed={seed} {encoding}: {r['result']} ({r['check_seconds']:.3f}s)",flush=True)
if __name__=='__main__':main()
