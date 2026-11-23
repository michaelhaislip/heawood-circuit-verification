# Star-cover follow-up: reuse of an existing formal construction

The proposed general star-cover theorem was already formalized in the pinned
upstream project. The earlier assertion that it had not been formalized was
incorrect. This follow-up reuses that implementation instead of duplicating it.
No mathematical or first-formalization novelty is claimed.

## Established here

`lean/StarCover.lean` gives checked adapters and examples in the `Monotone2`
model used by the Heawood artifact:

- `cover_monotone`: the upstream explicit builder produces an AND/OR circuit
  of fan-in at most two.
- `cover_correct`: when all listed endpoints are valid inputs and the cover
  meets every listed edge, the circuit computes exactly the listed edge
  function, in the same oriented-pair predicate used by L-meta-971.
- `cover_exact_active`: for a nonempty covered edge list, circuit size plus
  one equals the number of edge entries plus the number of active stars.
- `star_cover_spec`: combines correctness, exact active-star count, and the
  upper bound using total cover-list length.
- `graph_cover_upper`: for a finite simple graph with an edge and vertex
  cover T, constructs a Monotone2 circuit with size + 1 at most |E| + |T|.
- `heawood_correct`: instantiates the builder with the 21 Heawood edges and
  cover [0,1,2,3,4,5,6], proving correctness and size exactly 27.
- `empty_graph`: the empty edge list and empty cover produce the constant
  false function with zero gates, including on zero inputs.

The star, path, triangle, and redundant-cover examples check sizes 3, 4, 4,
and 3 respectively. The repeated cover entry and unused entries in the last
example emit no gates; only one star is active.

## Meaning of the count

Each edge is assigned to its first covering endpoint in the supplied cover
order. A nonempty star with d assigned edges uses d-1 OR gates and one AND
gate. Combining k stars needs k-1 further OR gates. Thus for m > 0:

    size = m + k - 1

Here k is the number of active stars, not necessarily the cover-list length.
Repeated or redundant cover entries may be inactive. For list inputs, m
counts edge entries, including any duplicates; use a list containing each
undirected edge once to interpret m as the graph's edge count. The graph
adapter obtains that representation from the upstream graph machinery.

This is the size of the constructed circuit, not a claim that it is minimal.
The Heawood 27-gate lower bound remains unproved. The generated circuit is
a different gate ordering from the original artifact's baseline; it computes
the same explicit target, but no syntactic equality of the two lists is claimed.

## Independent Lean verification

Use the same upstream checkout and dependency pins as the original artifact:

```text
git clone https://github.com/brilliant-hq/pequalnp-proofs.git upstream-proof
git -C upstream-proof checkout --detach 8ebf8f114c5d4568b533cb9864a4ea9b6ad5bbbc
cd upstream-proof/lean
lake exe cache get
lake build PEqualNP.MetaComplexity.Helpers.CoverCircuitGraph
lake env lean /absolute/path/to/star-cover/lean/StarCover.lean
```

Lean 4.36.0; Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842.
Do not run `lake update`. The command must exit zero. The three axiom audits
at the end must contain only propext, Classical.choice, and Quot.sound.
The successful local audit is preserved in `logs/star-cover-lean.log`.

## Existing formal results and attribution

The pinned project already contains:

- [CoverCircuitList.lean](https://github.com/brilliant-hq/pequalnp-proofs/blob/8ebf8f114c5d4568b533cb9864a4ea9b6ad5bbbc/lean/PEqualNP/MetaComplexity/Helpers/CoverCircuitList.lean):
  the explicit assignment, builder, correctness, bounds, and exact-size results.
  This follow-up directly reuses `gates_ops`, `circuitFun_eq`, `size_blocks`,
  `sum_blocks`, and `size_le`.
- [CoverCircuitGraph.lean](https://github.com/brilliant-hq/pequalnp-proofs/blob/8ebf8f114c5d4568b533cb9864a4ea9b6ad5bbbc/lean/PEqualNP/MetaComplexity/Helpers/CoverCircuitGraph.lean):
  the simple-graph representation and general upper bound, with an exact-size
  variant obtained by padding.
- [EdgeUpperMono.lean](https://github.com/brilliant-hq/pequalnp-proofs/blob/8ebf8f114c5d4568b533cb9864a4ea9b6ad5bbbc/lean/PEqualNP/MetaComplexity/Helpers/EdgeUpperMono.lean):
  an earlier general existence proof via a compositional builder.

The new file provides a thin compatibility layer and concrete applications.
It is AI-assisted work developed with OpenAI Codex and distributed under
Apache-2.0 with the upstream implementation credited. It has been checked
locally and is included in artifact version 0.2.0. It has not been accepted
by the fleet.
