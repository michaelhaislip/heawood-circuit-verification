"""Independent standard-library audit of stored protocol and SAT witnesses."""
import hashlib,json,pathlib
root=pathlib.Path(__file__).resolve().parent
manifest=root/'SHA256SUMS'
if manifest.exists():
    for line in manifest.read_text(encoding='utf-8').splitlines():
        digest,name=line.split('  ',1)
        assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
rs=[json.loads(l)for l in (root/'results/portfolio-results.jsonl').read_text(encoding='utf-8').splitlines()]
trials=[r for r in rs if 'arm'in r]
assert len(trials)==20
assert {(r['size'],r['base_seed'],r['arm'])for r in trials}=={
 (size,seed,arm)for size in [9,10]for seed in [100,102,104,106,108]for arm in ['single','portfolio']}
checked=0
for r in trials:
    seed=r['base_seed']
    configs=[('ite',seed,12)]if r['arm']=='single'else[
      ('ite',seed,3),('implication',seed,3),('ite',seed+1,3),('implication',seed+1,3)]
    assert r['configured_solver_budget_s']==12
    assert r['result']==r['attempts'][-1]['result']
    assert len(r['attempts'])<=len(configs)
    for i,a in enumerate(r['attempts']):
        assert (a['encoding'],a['seed'],a['timeout_s'])==configs[i]
        assert a['normalize']is True and a['gates']==r['size']and a['n']==7
        if i<len(r['attempts'])-1:assert a['result']=='unknown'
        if a['result']=='unknown':assert a['reason']=='timeout'
        if a['result']!='sat':continue
        for mask in range(1<<a['n']):
            w=[bool(mask>>j&1)for j in range(a['n'])]+[False,True]
            for op,u,v in a['witness']:
                assert op in (0,1)and 0<=u<len(w)and 0<=v<len(w)
                w.append((w[u]and w[v])if op==0 else(w[u]or w[v]))
            assert w[-1]==bool(any(mask>>u&1 and mask>>v&1 for u,v in a['edges']))
        checked+=1
print(json.dumps({'status':'PASS','paired_trials':10,'strategy_runs':20,
  'SAT_attempts_independently_rechecked':checked,'protocol_and_checksums':'PASS',
  'UNSAT_certification':False},indent=2))
