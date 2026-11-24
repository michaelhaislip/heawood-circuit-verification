# Heawood edge-function verification artifact

This artifact gives a locally kernel-checked Lean formalization of a 27-gate
monotone circuit and a boundary-based correctness method for the explicit
14-variable Heawood edge function. It does **not** prove that 27 gates are
necessary, settle P versus NP, or claim fleet acceptance or mathematical novelty.

## Contents and status

| File | Purpose |
| --- | --- |
| `lean/HeawoodBoundary.lean` | Authoritative Lean definitions and proofs, unchanged from the successful check |
| `lean/StarCover.lean`, `STAR_COVER.md` | Reuse of the upstream general construction, compatibility proofs, examples, and independent verification instructions |
| `followups/alias-deletion/` | General boundary-alias deletion, alias-free existence theorem, finite example, and its own verification script |
| `followups/normalization-audit/` | Checked padding/essentiality lemmas and a scope counterexample; full normalization remains unproved |
| `benchmarks/` | Diagnostic scripts, raw results, and independent SAT-witness audits; not formal lower-bound proofs |
| `data/heawood.json` | Exact 21 edges, 21 positive masks, 37 negative masks, and all 27 gates |
| `verify.py` | Standard-library exhaustive verifier; also checks that JSON agrees with the Lean literals |
| `upstream/CircuitLowerBounds.lean` | Exact upstream gate, circuit, evaluation, and size definitions for inspection |
| `upstream/MetaComplexityLgpMono.lean` | Exact upstream `Monotone2` definition for inspection |
| `PROVENANCE.json`, `upstream/lake-manifest.json` | Immutable source and dependency pins |
| `logs/` | Original axiom audit and artifact recheck output |
| `search/`, `data/heawood971-*` | Optional solver experiments and original outcomes |
| `RELATED_WORK.md` | Prior-art search, attribution, and limits on novelty claims |
| `FLEET.md` | Current contribution rules and delivery status |
| `SHA256SUMS` | Checksums for all packaged files except this checksum file |

## Function, circuit model, and witness

For the edge list in `data/heawood.json`, the target is
`f(x) = OR_{(u,v) in E} (x[u] AND x[v])`.
Masks encode vertex `i` in bit `i`, with bit 0 least significant.

The formal model is the fleet's `CircuitLowerBounds.Circuit`. Input wires are
0 through 13; gate number `j`, starting at 0, produces wire `14+j`. A read of
a wire that does not yet exist returns false. Size is the number of gates.
`Monotone2` allows AND/OR gates with at most two operands, including constant
and copy gates; every gate counts. Our witness uses exactly two operands per
gate, all referring to existing wires, and outputs wire 40. There are no
implicit constant wires in this witness.

The construction groups the 21 edges into seven three-edge stars centered
at vertices 0 through 6. Each star uses two ORs and one AND; six further ORs
combine the seven outputs: `7*(2+1)+6 = 27` gates. The stored gate order is a
topological reordering of that construction. The exact list is in the Lean
`baseline` definition and in JSON.

## Independent verification

Python 3.10 or later, with no third-party packages, is sufficient for:

```text
python verify.py
```

Run from the artifact directory (or give the absolute script path). Expected:
`PASS`, 16,384 inputs checked, 27 gates, 21 minimal true inputs, 37 maximal
false inputs, matching Lean literals, and six inconclusive search cases.
Do not use Python's `-O` flag: the verifier uses assertions.

For the formal check, install Git and elan with Lake, then create a separate
checkout. Network access and substantial disk space are needed for Mathlib.
Do not run `lake update`; the checked dependency versions must stay pinned.

```text
git clone https://github.com/brilliant-hq/pequalnp-proofs.git upstream-proof
git -C upstream-proof checkout --detach 8ebf8f114c5d4568b533cb9864a4ea9b6ad5bbbc
cd upstream-proof/lean
lake exe cache get
lake build PEqualNP.Defs
lake env lean /absolute/path/to/heawood971/lean/HeawoodBoundary.lean
```

Use an absolute Windows path on Windows. The pinned toolchain is
Lean 4.36.0 and Mathlib revision `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.
The last command must exit zero. It prints the axiom dependencies of
`Research.Heawood971.boundary_check` and `baseline_target`; both must contain
only `propext`, `Classical.choice`, and `Quot.sound`. The proof uses kernel
evaluation (`decide +kernel`), not native evaluation. Rechecking can take
several minutes and substantial memory. The two definition files included
for inspection are not a complete replacement for the pinned checkout.

## What Lean proves

`boundary_check` proves a generic sufficiency theorem: if each target-true
input lies above a listed accepted input, and each target-false input lies
below a listed rejected input, monotonicity implies correctness everywhere.
It establishes circuit monotonicity directly in the fleet model, including
out-of-bounds wire semantics.

`positive_cover` and `negative_cover` establish those coverage obligations
for the explicit Heawood boundary. `baseline_mono`, `baseline_size`, and
`baseline_correct` prove the witness is monotone, has 27 gates, and computes
the target. `baseline_target` expresses correctness using exactly the edge
predicate of L-meta-971.

The Lean proof establishes coverage of the concrete lists. The claims that
these are *exactly* all minimal true/maximal false inputs, and the JSON
transcription, are additionally checked exhaustively by Python. No separate
Lean theorem asserting minimality/maximality of every listed input is claimed.

## Search experiments: inconclusive

Optional dependencies are pinned in `search/requirements.txt`; use Python
3.12 or later for these pinned versions (the original runs used 3.13):

```text
python -m venv .venv
# Activate .venv with the command appropriate for your shell.
python -m pip install -r search/requirements.txt
python search/heawood971.py --facts
python search/heawood971.py --control --timeout 120
python search/heawood971.py --suite --size 26 --timeout 120
python search/heawood971_symmetry.py
```

The original six-case suite returned `unknown` because of timeout in every
case. The earlier first-edge/AND run also timed out. These results give no
lower bound, no UNSAT certificate, and no proof that a smaller circuit does
not exist. Timing and solver outcomes may differ across machines.

The SAT control fixes a known 27-gate circuit and returned SAT; its witness
was checked on all 16,384 inputs. Search scripts use a **different wire
convention**: inputs 0..13, implicit constants at 14 and 15, and gate j at
16+j. The JSON control log is preserved in that convention; the formal
baseline and `heawood.json` use the fleet convention. The search applies
alias-free active-prefix/copy-padding normalization and first-input-pair
symmetry reduction. Their completeness has not been formalized in Lean.
The automorphism/orbit checks are computational evidence only.

## Attribution and reuse

Circuit definitions and the monotonicity helper proof pattern come from
`brilliant-hq/pequalnp-proofs`, including `Outside/L_meta_616.lean`, at the
recorded revision. The artifact preserves the upstream Apache-2.0 license
in `upstream/LICENSE`; this package is distributed under that license.
Describe it as a reproducible supporting formalization, not a new lower
bound or a fleet-accepted contribution.
