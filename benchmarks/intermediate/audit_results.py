"""Audit packaged records and SAT witnesses without Z3 or third-party code."""
import collections,hashlib,json,pathlib
root=pathlib.Path(__file__).resolve().parent
manifest=root/'SHA256SUMS'
if manifest.exists():
    for line in manifest.read_text(encoding='utf-8').splitlines():
        digest,name=line.split('  ',1)
        assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
main=[json.loads(l)for l in (root/'results/intermediate-results.jsonl').read_text(encoding='utf-8').splitlines()]
ab=[json.loads(l)for l in (root/'results/normalization-ablation.jsonl').read_text(encoding='utf-8').splitlines()]
rs=[r for r in main if 'result'in r]
assert len(rs)==48 and len(ab)==12
assert len({(r['case'],r['gates'],r['encoding'],r['seed'])for r in rs})==48
assert len({(r['gates'],r['encoding'],r['seed'])for r in ab})==12
for r in rs+ab:
    if r['result']!='sat':continue
    for m in range(1<<r['n']):
        w=[bool(m>>i&1)for i in range(r['n'])]+[False,True]
        for op,a,b in r['witness']:
            assert op in (0,1)and 0<=a<len(w)and 0<=b<len(w)
            w.append((w[a]and w[b])if op==0 else(w[a]or w[b]))
        expected=any(m>>a&1 and m>>b&1 for a,b in r['edges'])
        assert w[-1]==bool(expected)
assert all(r['reason']=='timeout'for r in rs+ab if r['result']=='unknown')
print(json.dumps({'status':'PASS','runs':len(rs+ab),'outcomes':dict(collections.Counter(r['result']for r in rs+ab)),
 'SAT_witnesses_rechecked':sum(r['result']=='sat'for r in rs+ab),
 'note':'UNSAT verdicts are not independently certified'},indent=2))
