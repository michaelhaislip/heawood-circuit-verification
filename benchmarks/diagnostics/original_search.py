"""Investigate L-meta-971. Solver results here are not Lean proofs.

For monotone circuits, accepting every edge pair and rejecting every
maximal independent set is equivalent to the full edge-function table:
every true input contains an edge, and every false input extends to a
maximal independent set. Witnesses are still evaluated on all 16,384 inputs.
"""
import argparse
import itertools
import json
import pathlib
import sys
import time
import z3

EDGES = [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
         (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),
         (6,8),(6,9),(6,11)]
N = 14
EDGE_MASKS = [(1 << a) | (1 << b) for a, b in EDGES]


def target(mask):
    return any(mask & e == e for e in EDGE_MASKS)


INDEPENDENT = [mask for mask in range(1 << N) if not target(mask)]
MAXIMAL_FALSE = [mask for mask in INDEPENDENT
                 if all(target(mask | (1 << v)) for v in range(N) if not mask >> v & 1)]
ROWS = EDGE_MASKS + MAXIMAL_FALSE


def evaluate(gates, mask):
    values = [bool(mask >> v & 1) for v in range(N)] + [False, True]
    for op, a, b in gates:
        assert a < len(values) and b < len(values)
        values.append(values[a] and values[b] if op == 0 else values[a] or values[b])
    return values[-1]


def known_upper():
    gates = []
    terms = []
    for u in range(7):
        neighbors = [v for a, v in EDGES if a == u]
        for op, a, b in [(1, neighbors[0], neighbors[1]),
                         (1, N + 2 + len(gates), neighbors[2])]:
            gates.append([op, a, b])
        gates.append([0, u, N + 2 + len(gates) - 1])
        terms.append(N + 2 + len(gates) - 1)
    out = terms[0]
    for term in terms[1:]:
        gates.append([1, out, term])
        out = N + 2 + len(gates) - 1
    # Kahn ordering with the same lexicographic rule used by the encoder.
    mapped = {v: v for v in range(N + 2)}
    ordered = []
    remaining = set(range(len(gates)))
    while remaining:
        ready = []
        for j in remaining:
            op, a, b = gates[j]
            if a in mapped and b in mapped:
                ready.append(((op, *sorted([mapped[a], mapped[b]])), j))
        gate, j = min(ready)
        ordered.append(list(gate))
        mapped[N + 2 + j] = N + 2 + len(ordered) - 1
        remaining.remove(j)
    assert len(ordered) == 27
    assert all(evaluate(ordered, mask) == target(mask) for mask in range(1 << N))
    return ordered


def solve(size, timeout, first=None, first_op=None, fixed=None):
    width = len(ROWS)
    solver = z3.SolverFor('QF_BV')
    solver.set(timeout=timeout * 1000)
    wires = [z3.BitVecVal(sum(1 << j for j, row in enumerate(ROWS) if row >> v & 1), width)
             for v in range(N)] + [z3.BitVecVal(0, width), z3.BitVecVal((1 << width) - 1, width)]
    bits = (N + 2 + size).bit_length()
    gates = []
    active = []

    def select(index, choices):
        result = choices[-1]
        for k in reversed(range(len(choices) - 1)):
            result = z3.If(index == k, choices[k], result)
        return result

    for j in range(size):
        op = z3.BitVec(f'op{j}', 1)
        a, b = z3.BitVecs(f'a{j} b{j}', bits)
        solver.add(z3.ULT(a, len(wires)), z3.ULT(b, len(wires)), z3.ULE(a, b))
        va, vb = select(a, wires), select(b, wires)
        value = z3.BitVec(f'v{j}', width)
        solver.add(value == z3.If(op == 0, va & vb, va | vb))
        live = z3.Bool(f'live{j}')
        if j == 0:
            solver.add(live)
        else:
            solver.add(z3.Implies(live, active[-1]))
            solver.add(z3.Implies(z3.Not(live), z3.And(op == 0, a == N + 1 + j, b == a)))
        # A smallest boundary-correct circuit has no aliases or constant gates.
        # Shorter circuits remain represented by a suffix of copy gates.
        solver.add(z3.Implies(live, z3.And(z3.ULT(a, b), a != N, a != N + 1,
                                          b != N, b != N + 1,
                                          *[value != old for old in wires])))
        if j:
            pop, pa, pb = gates[-1]
            reads_previous = z3.Or(a == N + 1 + j, b == N + 1 + j)
            solver.add(z3.Or(reads_previous,
                             z3.ULE(z3.Concat(pop, pa, pb), z3.Concat(op, a, b))))
        gates.append((op, a, b))
        active.append(live)
        wires.append(value)
    for j in range(size - 1):
        wire = N + 2 + j
        solver.add(z3.Or(*[z3.Or(a == wire, b == wire) for _, a, b in gates[j + 1:]]))
    for v in range(N):
        solver.add(z3.Or(*[z3.Or(a == v, b == v) for _, a, b in gates]))
    solver.add(wires[-1] == (1 << len(EDGE_MASKS)) - 1)
    if first is not None:
        a, b = {'same-side': (0,1), 'edge': (0,7), 'nonedge': (0,9)}[first]
        solver.add(gates[0][1] == a, gates[0][2] == b)
    if first_op is not None:
        solver.add(gates[0][0] == first_op)
    if fixed is not None:
        for actual, expected in zip(gates, fixed, strict=True):
            solver.add(*[a == b for a, b in zip(actual, expected)])
    began = time.monotonic()
    result = solver.check()
    record = {'size': size, 'first': first, 'first_op': first_op,
              'result': str(result), 'seconds': round(time.monotonic() - began, 3),
              'rows': width, 'maximal_false_rows': len(MAXIMAL_FALSE),
              'lean_proof': False}
    record['model'] = 'alias-free active prefix with copy padding; constants eliminated'
    if result == z3.sat:
        model = solver.model()
        witness = [[model.eval(v).as_long() for v in gate] for gate in gates]
        assert all(evaluate(witness, mask) == target(mask) for mask in range(1 << N))
        record['gates'] = witness
        record['full_truth_table_checked'] = 1 << N
    elif result == z3.unknown:
        record['reason'] = solver.reason_unknown()
    return record


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--size', type=int, default=26)
    parser.add_argument('--timeout', type=int, default=180)
    parser.add_argument('--first', choices=['same-side','edge','nonedge'])
    parser.add_argument('--first-op', type=int, choices=[0,1])
    parser.add_argument('--facts', action='store_true')
    parser.add_argument('--control', action='store_true')
    parser.add_argument('--suite', action='store_true')
    args = parser.parse_args()
    if args.facts:
        print(json.dumps({'n': N, 'edges': len(EDGES), 'independent_sets': len(INDEPENDENT),
                          'maximal_independent_sets': len(MAXIMAL_FALSE),
                          'max_independent_size': max(m.bit_count() for m in INDEPENDENT),
                          'minimum_vertex_cover': N - max(m.bit_count() for m in INDEPENDENT),
                          'maximal_independent_sizes': sorted(m.bit_count() for m in MAXIMAL_FALSE),
                          'rows': len(ROWS)}), flush=True)
    elif args.control:
        print(json.dumps(solve(27, args.timeout, fixed=known_upper())), flush=True)
    elif args.suite:
        for first in ['same-side', 'edge', 'nonedge']:
            for op in [0, 1]:
                print(json.dumps(solve(args.size, args.timeout, first, op)), flush=True)
    else:
        print(json.dumps(solve(args.size, args.timeout, args.first, args.first_op)), flush=True)


if __name__ == '__main__':
    main()
