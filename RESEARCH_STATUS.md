# Research status: final session snapshot

Release v0.3.0 wraps up this research session. There is no running search,
desk polling, active fleet assignment, or promised future maintenance. The
repository is left open for inspection and reuse, rather than marked read-only.

## Established and reusable

| Result | Evidence | Intended use |
| --- | --- | --- |
| Explicit 27-gate Heawood construction, correct on every input | Lean proof, permitted axiom audit, independent check on all 16,384 inputs | Reference witness and regression case |
| Verification from 21 positive and 37 negative boundary cases | Generic monotonicity/coverage theorem in Lean; concrete coverage checked in Lean | Check future monotone circuit candidates |
| Star-cover adapters and worked examples | Lean reuse of already existing upstream builder and theorems | Apply a standard upper-bound construction to other graphs |
| Boundary-relative alias deletion | Lean proof of correctness, cleanliness, monotonicity, and exact one-gate decrease | One component of a justified normalization |
| Alias-free clean representative exists without increasing size | Lean least-size argument using boundary-relative deletion | Exclude boundary aliases within the stated clean-circuit class |
| Exact-budget copy padding and graph essentiality facts | Lean proofs | Other isolated normalization steps |
| A scope failure in generalized normalization | Lean counterexample plus SAT/UNSAT reproduction | Reject unsupported isolated-input cases before interpreting search results |

The boundary principle, star-cover construction, and upstream pointwise
deletion machinery are existing mathematics/formal work. Our contribution is
the recorded formalization, compatibility layers, examples, and reproducible
experiments. No priority or mathematical novelty is claimed; equivalence to
other unpublished or differently named formalizations has not been ruled out.

## Experimental findings

- The original six Heawood searches all timed out. They establish no lower bound.
- An instrumented Heawood case spent about 0.26 seconds constructing constraints
  and 120.6 seconds inside the solver. Active SAT search was observed, but
  preprocessing/search time shares and the exact causes of all historical
  timeouts remain unknown. An alternative encoding also timed out.
- Forty-eight tiny-case checks agreed with independent exhaustive enumeration.
  This tests the encoder on those instances, not arbitrary normalization completeness.
- Sixty intermediate/ablation runs showed a strong normalization benefit on
  the six-cycle (12/12 completed versus 4/12 without it), but no overall
  winner between the two encodings in the main suite (20/24 each).
- In ten paired strategy trials, a four-attempt portfolio and a single longer
  run solved the same five ten-gate cases and none of the five nine-gate cases.
  The portfolio reduced one slow run but had a slightly worse median and
  extra restart overhead. No general performance improvement was established.

Every recorded SAT witness in the audited benchmark packages has been checked
on its full truth table. Solver UNSAT verdicts have no independently checked
refutation certificates and must not be described as formal lower bounds.

## Unresolved

1. Whether every Heawood monotone circuit needs at least 27 gates.
2. Completeness of the full search normalization. Alias deletion and padding
   are components, not the entire reduction chain. Initial cleanup, constants,
   output/liveness conventions, canonical topological ordering, symmetry
   compatibility, and the SMT representation bridge still need justification.
3. Whether a proposed future solver refutation can be transported into the
   fleet model and checked by an allowed proof procedure.
4. Independent human review, third-party adoption, and fleet acceptance.

The isolated-vertex counterexample does not invalidate the Heawood or cycle
benchmarks, whose graphs have no isolates. It demonstrates why the generalized
encoder cannot claim unqualified completeness. Historical scripts are retained
unchanged; the normalization audit includes a guarded research variant.

## Reuse and independent checking

Start with the root README and VERIFICATION.md. Each follow-up and benchmark
directory contains its own instructions and raw records. The proof project is
pinned to upstream commit 8ebf8f114c5d4568b533cb9864a4ea9b6ad5bbbc, Lean 4.36.0,
and Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842. Do not update dependencies
when reproducing the recorded checks. The release includes source and logs,
not generated Lean binaries.
`python audit_research.py` repeats stored SAT-witness checks and validates
the benchmark record structure without installing Z3. It does not validate
UNSAT refutations or replace Lean verification.

The most substantial unpublished-at-v0.2.0 component now included is
`followups/alias-deletion`: its example verifies deletion when internal wires
agree only on the boundary and genuinely differ elsewhere.

This is an AI-assisted verified computational research artifact under
Apache-2.0. Correctness claims rest on the stated checks and assumptions.
There is no claim of resolving P versus NP, a breakthrough, or fleet endorsement.
