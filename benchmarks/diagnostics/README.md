# Circuit search diagnostics

AI-assisted diagnostic experiment, 2026-11-23. This is computational evidence,
not a Lean proof, UNSAT certificate, or new circuit lower bound.

## Measured outcomes

Four tiny graphs were independently enumerated using full truth tables:
one edge (minimum 1), a two-edge star (2), a triangle (4), and two disjoint
edges (3). Exhaustive breadth-first enumeration over available Boolean
functions is independent of the SMT encoder. It allows free constants,
which relaxes the circuit model. All 48 SMT checks matched the oracle:
below/at/above the minimum, normalization off/on, and both encodings.
Every SAT witness was separately checked on every input. These tests do
not prove completeness of the search normalization for arbitrary graphs.

The two Heawood runs searched 26 gates with first gate AND(0,7), 58 boundary
rows, normalization enabled, seed 0, and a 120-second solver timeout. The
baseline is a generalized equivalent reconstruction of the original search
constraints, not a replay of its identical serialized formula. The alternative
changes wire selection from nested conditionals to guarded equalities:
the selected value equals wire k whenever the operand index equals k.
Operand index bounds make the two selection definitions equivalent.

| Encoding | Build s | Serialize s | Solver wall s | Solver CPU s | Decisions | Conflicts | Z3 max memory | SMT text bytes | Outcome |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| ite | 0.258 | 0.195 | 120.625 | 111.64 | 489,392 | 175,798 | 343.07 | 238,349 | unknown (timeout) |
| implication | 0.326 | 0.193 | 120.052 | 110.62 | 606,550 | 202,501 | 140.71 | 217,958 | unknown (timeout) |

Boundary generation is timed separately in the raw records. Formula text
length measures the serialized expression, not the size of the eventual
SAT clause database. Z3 statistics include created clauses, propagations,
restarts, reported memory, and resource counts. Some allocation/resource
statistics are process/context cumulative; they are not independent per-run
work measurements or percentages of completion.

The implication encoding used less solver-reported peak memory in this
single pair of fresh-process runs (140.71 versus 343.07 in Z3's reported
memory units). Both timed out. More decisions or conflicts in the same
budget do not show that it came closer to finding a circuit or proving UNSAT.
On the tiny cases every solver call finished within 0.03 seconds, too short
and too few repetitions to support a reliable encoding speed ranking.

## What this diagnoses

For the baseline rerun, Python constraint construction is negligible compared
with `check()`. The solver performed extensive SAT search before reporting
timeout. The observed failure was not a Python build delay or a reported
out-of-memory error. `check()` includes preprocessing as well as search;
these measurements do not isolate their respective time shares.

The original six runs did not collect these diagnostics. This one recreated
case supports an explanation of that failure pattern, but cannot establish
the exact cause or internal behavior of all six historical runs. Neither
timeout shows that no 26-gate circuit exists. Conflict counts are not a
measure of distance from a solution, nor are fewer conflicts necessarily
better. A single seed and tiny validation instances cannot establish a
general encoding winner. CPU/wall-time differences also reflect scheduling
and operating-system work, not a measured proof-search stage.

## Next experiment

Use intermediate, independently checked instances that take seconds rather
than milliseconds. Run several seeds and compare completion rate and median
runtime under equal budgets, including normalization ablations. If topology
partitioning is attempted, validate partition coverage before interpreting
UNSAT. Retain the original six timeouts as inconclusive. Simply changing
the wire-selection encoding has not established a solution to the bottleneck.

## Reproduction

Use Python 3.10 or later and install requirements.txt in a virtual environment:

```text
python -m pip install -r requirements.txt
python -u circuit_benchmark.py --timeout 15 > small.jsonl
python -u circuit_benchmark.py --heawood --encoding ite --timeout 120 > heawood-ite.jsonl
python -u circuit_benchmark.py --heawood --encoding implication --timeout 120 > heawood-implication.jsonl
```

Do not run Python with -O: assertions validate the results. Run the two large
experiments sequentially to avoid intentional CPU contention. Timings and
solver outcomes can vary across machines. Environment versions are recorded
in each result file. Included in release v0.3.0; no fleet acceptance is claimed.

Z3 parameter documentation (timeout is in milliseconds):
https://microsoft.github.io/z3guide/programming/Parameters/

The encoding derives from the AI-assisted Heawood artifact's search script,
preserved as original_search.py for inspection. Apache-2.0; see LICENSE.
The underlying circuit model and original proof attribution are recorded at:
https://github.com/michaelhaislip/heawood-circuit-verification
