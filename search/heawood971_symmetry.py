"""Explicit graph automorphisms supporting the six first-gate search cases."""
import json
import pathlib
from heawood971 import EDGES, N
import networkx as nx

g = nx.Graph()
g.add_nodes_from(range(N))
g.add_edges_from(EDGES)
permutations = [list(p[i] for i in range(N))
                for p in nx.algorithms.isomorphism.GraphMatcher(g, g).isomorphisms_iter()]
assert len(permutations) == 336
for p in permutations:
    assert sorted(p) == list(range(N))
    assert all(g.has_edge(u, v) == g.has_edge(p[u], p[v]) for u in range(N) for v in range(N))
reps = {'same-side': (0, 1), 'edge': (0, 7), 'nonedge': (0, 9)}
orbits = {name: sorted(set(tuple(sorted((p[a], p[b]))) for p in permutations))
          for name, (a, b) in reps.items()}
assert sorted(map(len, orbits.values())) == [21, 28, 42]
assert len(set(pair for orbit in orbits.values() for pair in orbit)) == 91
result = {'automorphisms': len(permutations), 'orbits': orbits,
          'interpretation': 'Three orbits of unordered distinct input pairs; two gate operations',
          'lean_proof': False}
pathlib.Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'automorphisms': len(permutations), 'orbit_sizes': {k: len(v) for k,v in orbits.items()}}))
