# Normalization completeness: bounded audit

AI-assisted research, 2026-11-23. **The full search normalization is not yet
proved complete.** This audit verifies limited steps, identifies a concrete
scope failure outside the Heawood setting, and maps the remaining obligations.
No Heawood lower bound or general correctness theorem for the SMT encoder
is established. No mathematical novelty is claimed.

## Concrete scope counterexample

On three inputs with only edge (0,1), the function x0 AND x1 has a one-gate
monotone circuit. Input 2 is isolated and irrelevant. The legacy normalized
encoder requires all three inputs to appear in gate operands, which a single
two-input gate cannot satisfy. The recorded experiment returns SAT without
normalization and UNSAT with normalization.

Lean independently verifies both the one-gate construction and the impossibility
of covering three distinct input indices with two operand indices. This is a
counterexample to *unqualified* normalization completeness, not to the
Heawood graph-specific hypothesis. Heawood, the matching benchmarks, and the
cycle benchmarks have no isolated vertices; this example does not invalidate
their outcomes. Their UNSAT results nevertheless remain uncertified.

The active research encoder now rejects isolated-input normalized searches
and requires a nonempty loopless graph with valid endpoints. This guard is
a necessary scope check, not a certificate that the remaining normalization
is complete. Historical scripts and results are preserved unchanged.

## Verified bounded lemmas

`lean/NormalizationAudit.lean` has passed Lean 4.36.0:

- `binary_commutes` and `binary_idempotent`: the local AND/OR identities
  behind operand sorting and duplicate-operand elimination.
- `copyPad_eval`, `copyPad_mono`, `copyPad_size`: appending an AND copy of
  the output preserves the function and monotonicity and adds exactly one gate.
- `copyPad_last`, `copyPad_suffix`: the copy's output is the last new wire;
  if the old output was last, the appended gate reads the previous wire twice,
  matching the encoder's inactive suffix convention after index translation.
- `pad_to_budget`: any Monotone2 circuit of size at most s can be extended
  to exactly s gates without changing its function. This alone does not
  establish the other active-prefix, liveness, or ordering constraints.
- `singleEdge_spec` and `one_gate_all_reads_impossible`: the scope example.
- `graph_singleton_false` and `graph_not_projection`: a simple graph's edge
  function is false on singleton inputs and is not an input projection.
- `graph_vertex_essential` and `no_isolates_all_essential`: every vertex
  with a neighbor is an essential variable of the graph edge function.

The main audited theorems depend only on propext, Classical.choice, and
Quot.sound (the index-counting lemma needs only propext and Quot.sound).
The file has no proof holes or new axioms. These are standalone lemmas,
not an end-to-end normalization theorem.

## Rule-by-rule review

| Encoder restriction | Justification or prerequisite | Status |
| --- | --- | --- |
| Only binary AND/OR gates in active prefix | Propagate constants, remove copies and repeated operands from an initially fan-in-at-most-two circuit | Local identities verified; whole-circuit reduction unproved here |
| Implicit free constants, then prohibit their active use | Nonconstant target; constant propagation must not increase gate count | Scope identified; full bridge to fleet's counted-constant model unproved |
| No active boundary-signature aliases | Delete a gate and redirect all readers to an earlier wire agreeing on every boundary row | Existing upstream pointwise deletion lemma is a building block; boundary/minimality/Monotone2 integration remains |
| Every nonoutput gate is read later | Remove the unused output cone and reindex; keep output last | Plausible constructive reduction, not verified here |
| Every input occurs in some operand list | All inputs essential and target not a lone input projection; prove unread inputs cannot affect output | Essential-input and nonprojection hypotheses verified for nonisolated simple graphs; circuit-support bridge not assembled |
| Sort operands a < b | Commutativity plus repeated-operand elimination | Boolean identities verified; global rewrite still needed |
| Sort adjacent independent gates by numeric key | Choose a lexicographically least valid topological enumeration, correctly rewriting indices and preserving output position | Main unproved ordering obligation |
| Active prefix followed by copies | First reduce to a nonempty minimal circuit with output last, then pad | Copy preservation and suffix shape verified; existence of the required prefix remains |
| First gate in one of six Heawood cases | Graph automorphisms give three input-pair orbits; both operations considered | Automorphisms checked computationally earlier, not in Lean; compatibility with ordering unproved |
| Fixed final output and offset n+2 | Delete irrelevant gates, place output last, translate the two implicit constant slots | Representation bridge unproved |

The ordering and first-gate symmetry reductions must be proved jointly or
shown to preserve each other's constraints. Relabeling a sorted circuit may
unsort it. This observation is a proof obligation, not a demonstrated flaw
in the six-case Heawood split. A global minimality argument over both
topological orderings and automorphism images is one possible route, but
has not been verified here.

Boundary equality is enough for the *final monotone output* by the prior
checked boundary theorem. Internal wires equal on boundary rows need not
be globally equal, so the alias-removal proof must use pointwise preservation
on those rows, then reapply the boundary theorem; it must not assume global
wire equality.

## Existing upstream building blocks

At pinned revision 8ebf8f114c5d4568b533cb9864a4ea9b6ad5bbbc:

- `MetaComplexity/Helpers/EdgeFnModel.lean`: `rdel_length`, `rdel_clean`,
  and `rdel_all` prove deletion and redirection where the two wires agree.
  Their `CleanL` interface needs explicit connection to this encoder's model.
- `Readers.lean`: dead-gate and alias reductions for its least clean lists.
- `Elim.lean`: constant/alias propagation for a fixed-input circuit operation;
  this is related infrastructure, not automatically the required normalization.
- `Support.lean`: semantic support infrastructure, relevant to unread inputs.

Sources live under:
https://github.com/brilliant-hq/pequalnp-proofs/tree/8ebf8f114c5d4568b533cb9864a4ea9b6ad5bbbc/lean/PEqualNP

## Bounded next proof target

Prove boundary-relative alias deletion for a *clean monotone binary circuit*
by instantiating `rdel_all`, preserving its gate operations, and transporting
the output through the index renaming. Establish the one-gate size decrease.
Then connect that reduction to the already checked monotone boundary theorem.
This isolates one substantive completeness obligation without tackling the
full canonical ordering or automorphism argument. It is not completed here.

Until the entire reduction chain and the Boolean/bit-vector encoding bridge
are checked, an SMT UNSAT result remains computational evidence. A checked
refutation certificate would additionally be required for a formal lower bound.

## Independent verification

Use the original pinned checkout; do not run lake update:

```text
git clone https://github.com/brilliant-hq/pequalnp-proofs.git upstream-proof
git -C upstream-proof checkout --detach 8ebf8f114c5d4568b533cb9864a4ea9b6ad5bbbc
cd upstream-proof/lean
lake exe cache get
lake build PEqualNP.MetaComplexity.Helpers.CoverCircuitList
lake env lean /absolute/path/to/normalization-completeness-audit/lean/NormalizationAudit.lean
```

Expected: exit zero and only the permitted axioms in the printed audits.
Mathlib is pinned to fc4f59e577feb1a4956671bc04ac18aaaf8cd842. The preserved
log is `logs/lean-check.log`. The solver reproduction uses Python 3.10+:

```text
python -m pip install -r requirements.txt
python -c "from legacy_encoder import solve; print(solve(3,[(0,1)],1,5,normalize=False)['result']); print(solve(3,[(0,1)],1,5,normalize=True)['result'])"
python -c "from guarded_encoder import solve; solve(3,[(0,1)],1,5,normalize=True)"
```

The first command prints sat, then unsat. The guarded call intentionally
raises ValueError. Stored records are in `data/`. No large solver run is
needed to reproduce the counterexample. SHA256SUMS covers the payload.

AI-assisted work using OpenAI Codex; Apache-2.0, with upstream helpers
credited above. Included in release v0.3.0; not accepted by the fleet.
