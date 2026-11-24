"""Diagnostic experiments, not Lean proofs or lower-bound certificates."""
import argparse, hashlib, itertools, json, pathlib, platform, time
import z3

HEAWOOD=[(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
 (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
CASES={'edge':(2,[(0,1)]),'star2':(3,[(0,1),(0,2)]),
       'triangle':(3,[(0,1),(0,2),(1,2)]),'matching2':(4,[(0,1),(2,3)])}

def truth(n,edges,m): return any(m>>a&1 and m>>b&1 for a,b in edges)

def exhaustive_minimum(n,edges):
    """Independent full-table BFS over sets of available Boolean functions.

    A nonredundant AND/OR gate adds one new function. Constants are free,
    which only relaxes the model. Complement/nonmonotone gates are excluded.
    This enumeration does not use the SAT encoder or its symmetry rules.
    """
    start=time.perf_counter(); mask=(1<<(1<<n))-1
    inputs={sum(1<<m for m in range(1<<n) if m>>i&1) for i in range(n)}|{0,mask}
    target=sum(1<<m for m in range(1<<n) if truth(n,edges,m))
    states={frozenset()}; levels=[]
    for depth in range(8):
        levels.append(len(states))
        if target in inputs or any(target in s for s in states):
            return {'minimum':depth,'states_per_level':levels,'seconds':time.perf_counter()-start}
        nxt=set()
        for s in states:
            available=inputs|s
            for a,b in itertools.combinations(available,2):
                for v in (a&b,a|b):
                    if v not in available:
                        if v==target:
                            return {'minimum':depth+1,'states_per_level':levels,
                                    'seconds':time.perf_counter()-start}
                        nxt.add(s|{v})
        states=nxt
    raise RuntimeError('BFS exceeded intended tiny instances')

def solve(n,edges,size,timeout,encoding='ite',normalize=True,first=None,seed=0):
    if normalize:
        if n < 2 or not edges or any(a == b or not (0 <= a < n and 0 <= b < n) for a,b in edges):
            raise ValueError('Normalized graph search requires a nonempty loopless graph with valid endpoints')
        if {v for edge in edges for v in edge} != set(range(n)):
            raise ValueError('Normalized graph search requires no isolated input vertices; completeness is still unproved')
    start=time.perf_counter()
    edge_masks=[(1<<a)|(1<<b) for a,b in edges]
    negatives=[m for m in range(1<<n) if not truth(n,edges,m) and
       all(truth(n,edges,m|(1<<i)) for i in range(n) if not m>>i&1)]
    rows=edge_masks+negatives; width=len(rows)
    boundary_seconds=time.perf_counter()-start
    start=time.perf_counter(); solver=z3.SolverFor('QF_BV')
    solver.set(timeout=timeout*1000,random_seed=seed)
    wires=[z3.BitVecVal(sum(1<<j for j,m in enumerate(rows) if m>>i&1),width)
           for i in range(n)]+[z3.BitVecVal(0,width),z3.BitVecVal((1<<width)-1,width)]
    bits=(n+2+size).bit_length(); gates=[]; active=[]; mux_count=0
    def select(index,choices):
        nonlocal mux_count
        if encoding=='ite':
            result=choices[-1]
            for k in reversed(range(len(choices)-1)):
                result=z3.If(index==k,choices[k],result)
            return result
        result=z3.BitVec('mux'+str(mux_count),width); mux_count+=1
        for k,choice in enumerate(choices): solver.add(z3.Implies(index==k,result==choice))
        return result
    for j in range(size):
        op=z3.BitVec(f'op{j}',1); a,b=z3.BitVecs(f'a{j} b{j}',bits)
        solver.add(z3.ULT(a,len(wires)),z3.ULT(b,len(wires)),z3.ULE(a,b))
        va,vb=select(a,wires),select(b,wires); value=z3.BitVec(f'v{j}',width)
        solver.add(value==z3.If(op==0,va&vb,va|vb))
        if normalize:
            live=z3.Bool(f'live{j}')
            if j==0: solver.add(live)
            else:
                solver.add(z3.Implies(live,active[-1]))
                solver.add(z3.Implies(z3.Not(live),z3.And(op==0,a==n+1+j,b==a)))
            solver.add(z3.Implies(live,z3.And(z3.ULT(a,b),a!=n,a!=n+1,b!=n,b!=n+1,
                                            *[value!=old for old in wires])))
            if j:
                pop,pa,pb=gates[-1]
                solver.add(z3.Or(a==n+1+j,b==n+1+j,
                    z3.ULE(z3.Concat(pop,pa,pb),z3.Concat(op,a,b))))
            active.append(live)
        gates.append((op,a,b)); wires.append(value)
    if normalize:
        for j in range(size-1):
            solver.add(z3.Or(*[z3.Or(a==n+2+j,b==n+2+j) for _,a,b in gates[j+1:]]))
        for v in range(n): solver.add(z3.Or(*[z3.Or(a==v,b==v) for _,a,b in gates]))
    solver.add(wires[-1]==(1<<len(edge_masks))-1)
    if first:
        a,b,op=first
        solver.add(gates[0][1]==a,gates[0][2]==b,gates[0][0]==op)
    build_seconds=time.perf_counter()-start
    start=time.perf_counter(); smt=solver.sexpr().encode()
    serialization_seconds=time.perf_counter()-start
    before={k:solver.statistics().get_key_value(k) for k in solver.statistics().keys()}
    start=time.perf_counter(); cpu_start=time.process_time()
    result=solver.check(); check_seconds=time.perf_counter()-start
    check_cpu_seconds=time.process_time()-cpu_start
    stats=solver.statistics()
    record={'n':n,'edges':edges,'gates':size,'rows':width,'encoding':encoding,
      'normalize':normalize,'first':first,'seed':seed,'timeout_s':timeout,
      'boundary_seconds':boundary_seconds,'build_seconds':build_seconds,
      'serialization_seconds':serialization_seconds,'check_seconds':check_seconds,
      'check_cpu_seconds':check_cpu_seconds,
      'assertions':len(solver.assertions()),'smt_bytes':len(smt),'smt_sha256':hashlib.sha256(smt).hexdigest(),
      'result':str(result),'stats_before':before,
      'stats':{k:stats.get_key_value(k) for k in stats.keys()},'lean_proof':False}
    if result==z3.unknown: record['reason']=solver.reason_unknown()
    if result==z3.sat:
        model=solver.model(); gs=[[model.eval(v).as_long() for v in g] for g in gates]
        for m in range(1<<n):
            values=[bool(m>>i&1) for i in range(n)]+[False,True]
            for op,a,b in gs: values.append(values[a]&values[b] if op==0 else values[a]|values[b])
            assert values[-1]==bool(truth(n,edges,m))
        record.update(witness=gs,full_table_checked=1<<n)
    return record

def main():
    p=argparse.ArgumentParser(); p.add_argument('--heawood',action='store_true')
    p.add_argument('--encoding',choices=['ite','implication'],default='ite')
    p.add_argument('--timeout',type=int,default=120); a=p.parse_args()
    print(json.dumps({'environment':{'python':platform.python_version(),'z3':z3.get_version_string(),
        'platform':platform.system(),'processor':platform.machine()}}),flush=True)
    if a.heawood:
        r=solve(14,HEAWOOD,26,a.timeout,a.encoding,True,(0,7,0)); r['case']='heawood'
        print(json.dumps(r),flush=True)
    else:
        for name,(n,edges) in CASES.items():
            oracle=exhaustive_minimum(n,edges)
            print(json.dumps({'case':name,'independent_oracle':oracle}),flush=True)
            for size in [oracle['minimum']-1,oracle['minimum'],oracle['minimum']+1]:
                for normalize in [False,True]:
                    for encoding in ['ite','implication']:
                        r=solve(n,edges,size,a.timeout,encoding,normalize)
                        r['case']=name; r['expected']='unsat' if size<oracle['minimum'] else 'sat'
                        assert r['result']==r['expected'],r
                        print(json.dumps(r),flush=True)
if __name__=='__main__': main()
