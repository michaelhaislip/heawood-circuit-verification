"""Audit consolidated experimental records without Z3; not a proof checker."""
import json,pathlib,subprocess,sys
root=pathlib.Path(__file__).resolve().parent
def read(path):return [json.loads(l)for l in (root/path).read_text(encoding='utf-8-sig').splitlines()if l.strip()]
small=[r for r in read('benchmarks/diagnostics/results/small.jsonl')if 'result'in r]
assert len(small)==48 and all(r['result']==r['expected']for r in small)
large=[r for name in ['heawood-ite','heawood-implication']
       for r in read(f'benchmarks/diagnostics/results/{name}.jsonl')if 'result'in r]
assert len(large)==2 and all(r['result']=='unknown'and r['reason']=='timeout'for r in large)
count=0
for r in small:
    if r['result']!='sat':continue
    for m in range(1<<r['n']):
        w=[bool(m>>i&1)for i in range(r['n'])]+[False,True]
        for op,a,b in r['witness']:
            assert op in (0,1)and 0<=a<len(w)and 0<=b<len(w)
            w.append((w[a]and w[b])if op==0 else(w[a]or w[b]))
        assert w[-1]==bool(any(m>>a&1 and m>>b&1 for a,b in r['edges']))
    count+=1
print(json.dumps({'diagnostic_runs':50,'small_SAT_witnesses_rechecked':count,
                  'Heawood_reruns':'both inconclusive'},indent=2),flush=True)
for path in ['benchmarks/intermediate/audit_results.py','benchmarks/portfolio/audit_results.py']:
    subprocess.run([sys.executable,str(root/path)],check=True)
example=json.loads((root/'followups/normalization-audit/data/isolated-counterexample.json').read_text(encoding='utf-8-sig'))
assert [(r['normalize'],r['result'])for r in example]==[(False,'sat'),(True,'unsat')]
guard=json.loads((root/'followups/normalization-audit/data/guard-check.json').read_text(encoding='utf-8-sig'))
assert guard['isolated_vertex_input_rejected']is True and guard['valid_edge_control']=='sat'
print('Research record audit PASS; UNSAT verdicts remain uncertified.')
