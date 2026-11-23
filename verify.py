"""Independent standard-library verification, including agreement with Lean literals."""
import hashlib, json, pathlib, re
root = pathlib.Path(__file__).resolve().parent
manifest = root/'SHA256SUMS'
if manifest.exists():
    for line in manifest.read_text(encoding='utf-8').splitlines():
        digest, name = line.split('  ', 1)
        assert hashlib.sha256((root/name).read_bytes()).hexdigest() == digest, name
d = json.loads((root/'data/heawood.json').read_text(encoding='utf-8'))
n, edges, circuit = d['n'], d['edges'], d['circuit']
def target(m):
    return any((m >> a & 1) and (m >> b & 1) for a,b in edges)
def evaluate(m):
    w = [bool(m >> i & 1) for i in range(n)]
    for g in circuit['gates']:
        assert len(g['inputs']) == 2
        assert all(0 <= i < len(w) for i in g['inputs'])
        a,b = [w[i] for i in g['inputs']]
        assert g['op'] in ('and','or')
        w.append(a and b if g['op']=='and' else a or b)
    return w[circuit['output']]
positives = [(1<<a)|(1<<b) for a,b in edges]
negatives = [m for m in range(1<<n) if not target(m) and
             all(target(m|(1<<i)) for i in range(n) if not (m>>i&1))]
assert positives == d['positive_masks']
assert negatives == d['negative_masks']
assert len(set(positives)) == 21 and len(negatives) == 37
assert len(circuit['gates']) == 27 and circuit['output'] == 40
for m in range(1<<n):
    assert evaluate(m) == bool(target(m)), m
    if target(m):
        assert any(m&p == p for p in positives)
    else:
        assert any(m&q == m for q in negatives)
t=(root/'lean/HeawoodBoundary.lean').read_text(encoding='utf-8')
lean_edges=[list(map(int,p)) for p in re.findall(r'\((\d+), (\d+)\)',t.split('def heawoodEdges')[1].split('def edgePoint')[0])]
lean_neg=list(map(int,re.findall(r'bitPoint (\d+)',t.split('def negatives')[1].split('theorem positive_cover')[0])))
b=t.split('def baseline : Circuit :=')[1].split('theorem baseline_mono')[0]
lean_gates=[{'op':op,'inputs':[int(a),int(b)]} for op,a,b in re.findall(r'GateOp\.(and|or), \[(\d+), (\d+)\]',b)]
assert lean_edges==edges and lean_neg==negatives and lean_gates==circuit['gates']
assert int(re.search(r'output := (\d+)',b)[1])==circuit['output']
records=[json.loads(line) for line in (root/'data/heawood971-suite.jsonl').read_text(encoding='utf-8').splitlines() if line.strip()]
assert len(records)==6 and all(r['result']=='unknown' and r['reason']=='timeout' for r in records)
print(json.dumps({'status':'PASS','inputs_checked':1<<n,'gates':27,'minimal_true':21,
                  'maximal_false':37,'lean_literals_match':True,'search':'6 unknown/timeouts'},indent=2))
