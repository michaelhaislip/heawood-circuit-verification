"""Predeclared held-out-seed portfolio experiment on the seven-cycle."""
import argparse,json,pathlib,platform,random,subprocess,sys,time
import z3
from circuit_benchmark import solve
from intermediate_benchmark import CASES,upper_witness

def main():
    p=argparse.ArgumentParser();p.add_argument('--worker',action='store_true')
    p.add_argument('--size',type=int);p.add_argument('--seed',type=int)
    p.add_argument('--encoding');p.add_argument('--timeout',type=int)
    p.add_argument('--output',default='portfolio-results.jsonl');a=p.parse_args()
    n,edges=CASES['cycle7']
    if a.worker:
        print(json.dumps(solve(n,edges,a.size,a.timeout,a.encoding,True,seed=a.seed)),flush=True);return
    # Fixed before examining these results; seeds 100..109 were not in the pilot.
    seeds=[100,102,104,106,108]
    jobs=[(size,seed,arm)for size in [9,10]for seed in seeds for arm in ['single','portfolio']]
    random.Random(20261125).shuffle(jobs)
    with pathlib.Path(a.output).open('w',encoding='utf-8')as f:
        def emit(r):f.write(json.dumps(r)+'\n');f.flush()
        emit({'protocol':{'graph':'cycle7','sizes':[9,10],'base_seeds':seeds,
          'single':'ite(base seed), 12 solver seconds',
          'portfolio':'ite(base), implication(base), ite(base+1), implication(base+1); 3 solver seconds each; stop on sat/unsat',
          'normalization':True,'fresh_process_per_attempt':True,'parallelism':1,
          'schedule_seed':20261125,'budget_scope':'12 seconds configured solver time; setup/startup overhead measured separately',
          'lower_bound_status':'uncertified encoded UNSAT only'},
          'environment':{'python':platform.python_version(),'z3':z3.get_version_string(),'platform':platform.system()},
          'independent_upper_witness':upper_witness(n,edges)})
        for i,(size,seed,arm)in enumerate(jobs):
            attempts=[];start=time.perf_counter()
            configs=[('ite',seed,12)]if arm=='single'else[
                ('ite',seed,3),('implication',seed,3),('ite',seed+1,3),('implication',seed+1,3)]
            for enc,s,t in configs:
                proc=subprocess.run([sys.executable,str(pathlib.Path(__file__).resolve()),'--worker',
                    '--size',str(size),'--seed',str(s),'--encoding',enc,'--timeout',str(t)],
                    text=True,capture_output=True,timeout=t+60)
                if proc.returncode:raise RuntimeError(proc.stderr)
                r=json.loads(proc.stdout);attempts.append(r)
                if size==10:assert r['result']!='unsat',r
                if r['result']in ('sat','unsat'):break
            record={'case':'cycle7','size':size,'base_seed':seed,'arm':arm,'order':i,
              'configured_solver_budget_s':12,'result':attempts[-1]['result'],
              'solver_seconds':sum(r['check_seconds']for r in attempts),
              'solver_cpu_seconds':sum(r['check_cpu_seconds']for r in attempts),
              'end_to_end_seconds':time.perf_counter()-start,'attempts':attempts}
            emit(record)
            print(f"{i+1}/20 size={size} seed={seed} {arm}: {record['result']}; solver {record['solver_seconds']:.3f}s; end-to-end {record['end_to_end_seconds']:.3f}s",flush=True)
if __name__=='__main__':main()
