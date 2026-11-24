# Boundary-relative alias deletion

AI-assisted formalization, 2026-11-23. This artifact completes one bounded
step of the normalization audit: deleting an internal gate that agrees with
an earlier wire on a covering monotone boundary. It does not prove the whole
SMT normalization complete or establish a Heawood lower bound.

## What is established

For a clean monotone binary circuit C, gate position p, and earlier wire a:

1. If wire n+p and wire a agree on every listed positive and negative
   boundary input, delete gate p and redirect its readers to a.
2. The new circuit remains clean and Monotone2, and has exactly one fewer gate.
3. Its output agrees with C on those boundary inputs. If those inputs cover
   every target-true point from below and every target-false point from above,
   and C accepts/rejects the respective lists, the new circuit computes the
   target on every input by monotonicity.

`deleteAlias_boundary` states the combined result. It does not require the
two internal wires to agree away from the boundary.

`minimal_no_boundary_alias` proves that a globally minimum-size clean
monotone circuit for the target cannot contain such an alias.

`alias_free_representative` goes further: from any clean Monotone2 circuit
passing the boundary tests, there exists a clean Monotone2 circuit of no
greater size computing the same target, with no gate agreeing with an earlier
wire on all boundary rows. Its existence proof selects a least-size clean
representative and uses deletion to exclude aliases. It is not an executable
normalizer or a proof of the other search constraints.

## Assumptions and representation

The circuit model is the fleet's CircuitLowerBounds.Circuit with n input
wires, counted gates, and out-of-range reads returning false. CleanL requires
each gate to read earlier wires with a prescribed unary/binary shape; combined
with Monotone2, all gates are binary AND/OR gates. Thus a prior cleanup step
from arbitrary fan-in-at-most-two circuits remains outside this theorem.
The removed gate must exist (p < length), and a must satisfy a < n+p.

Deletion uses the upstream `rdel` and `rd` functions: earlier indices stay
fixed, the removed wire maps to a, and later indices decrease by one. The
output index is renamed as well; the removed gate may be the output gate.
This artifact does not add the SMT encoder's two implicit constant slots.
The translation between that representation and the fleet circuit model is
still a separate obligation.

The target may be any Boolean function for which the supplied boundary
coverage and circuit tests hold; no graph-specific or no-isolates assumption
is needed for this alias-deletion result. The proof also supports empty
lists when the stated hypotheses can be met.

## Verified example

The target is the edge function of the three-vertex path:

    f(x) = (x0 AND x1) OR (x1 AND x2).

Its boundary masks are positive [3,6] and negative [2,5], with vertex i in
bit i. The six-gate example has an earlier wire h = x0 OR x2 and a later
wire g computing majority-of-three. These wires agree on all four boundary
inputs, but differ on input mask 1. The output x1 AND g computes f.

Deleting g and redirecting its reader to h yields a five-gate clean monotone
circuit computing f on all eight inputs. The example deliberately retains
other dead gates: it demonstrates one deletion, not an optimal circuit.
`not_global_alias` formally checks that this is genuinely boundary-relative.

## Files and verification

- `lean/Boundary.lean`: the generic boundary theorem and monotonicity helpers,
  extracted from the original checked Heawood artifact; namespace changed
  to Research.Boundary, the graph-specific definitions omitted, and the
  project import narrowed to the circuit definitions actually used.
- `lean/AliasDeletion.lean`: deletion adapters and the general theorems.
- `lean/Example.lean`: concrete path example, boundary coverage, unequal
  off-boundary wire values, and six-to-five gate correctness result.
- `logs/`: successful local Lean axiom audits.
- `verify.ps1`: repeatable verification against the pinned upstream checkout.
- `SHA256SUMS`: checksums of packaged text sources and logs. Generated Lean
  binaries are intentionally excluded from the distribution.

Install elan/Lake and Git, then prepare the pinned project:

```text
git clone https://github.com/brilliant-hq/pequalnp-proofs.git upstream-proof
git -C upstream-proof checkout --detach 8ebf8f114c5d4568b533cb9864a4ea9b6ad5bbbc
cd upstream-proof/lean
lake exe cache get
```

From PowerShell, run the artifact's script with the checkout's lean directory:

```powershell
./verify.ps1 -ProjectLeanDirectory /absolute/path/to/upstream-proof/lean
```

Use appropriate absolute paths for your platform. The script compiles the
two local dependency modules before checking the example. For another shell,
run these commands from the pinned project's lean directory, setting ARTIFACT
to the absolute artifact directory and keeping the module path available:

```sh
export LEAN_PATH="$ARTIFACT/lean${LEAN_PATH:+:$LEAN_PATH}"
lake build +PEqualNP.MetaComplexity.Helpers.EdgeFnModel
lake env lean --root="$ARTIFACT/lean" -o "$ARTIFACT/lean/Boundary.olean" "$ARTIFACT/lean/Boundary.lean"
lake env lean --root="$ARTIFACT/lean" -o "$ARTIFACT/lean/AliasDeletion.olean" "$ARTIFACT/lean/AliasDeletion.lean"
lake env lean --root="$ARTIFACT/lean" "$ARTIFACT/lean/Example.lean"
```

Do not run lake update. Lean is 4.36.0; Mathlib revision is
fc4f59e577feb1a4956671bc04ac18aaaf8cd842. All checks must exit zero.
Printed theorem dependencies must be subsets of propext, Classical.choice,
and Quot.sound. The finite example uses kernel evaluation, not native
evaluation. No proof holes or new axioms are used.

## Attribution and remaining work

The pointwise deletion theorem, index renaming, size decrease, and cleanliness
preservation come from upstream EdgeFnModel.lean and EdgeFnPlan.lean at the
pinned revision, especially `rdel_all`, `rdel_length`, and `rdel_clean`:
https://github.com/brilliant-hq/pequalnp-proofs/blob/8ebf8f114c5d4568b533cb9864a4ea9b6ad5bbbc/lean/PEqualNP/MetaComplexity/Helpers/EdgeFnModel.lean

The generic boundary proof derives from the AI-assisted Heawood artifact,
whose monotonicity helper proof pattern credits upstream L_meta_616:
https://github.com/michaelhaislip/heawood-circuit-verification

This work combines those existing tools. No mathematical novelty or
first-formalization claim is made. It was developed with OpenAI Codex and
is distributed under Apache-2.0; see LICENSE.

The full normalization still needs initial cleanup, constant handling,
liveness/output placement, canonical topological ordering, symmetry
compatibility, and the integer/bit-vector representation bridge. A solver
refutation also needs an independently checked certificate before it can
support a formal lower bound. This bounded step does not close those gaps.

Included in release v0.3.0. Not accepted by the fleet.
