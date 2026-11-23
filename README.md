# Heawood circuit verification

A verified computational research artifact for the 14-variable Heawood
edge function, developed with AI assistance using OpenAI Codex.

- **Established:** a Lean-verified 27-gate monotone construction and its
  correctness for every input, using the fleet's exact circuit definitions.
- **Not established:** the proposed 27-gate lower bound. The smaller-circuit
  searches timed out and remain inconclusive.
- **Useful for:** reproducible formal verification and a foundation for
  future circuit searches, including a proved 58-case boundary check.

## Verify it

With Python 3.10 or later (no extra packages):

```sh
python verify.py
```

This checks all 16,384 inputs, the 27-gate witness, the 21 positive and 37
negative boundary cases, agreement with the Lean literals, and file hashes.
For independent Lean verification with pinned Lean 4.36.0 and Mathlib,
follow [VERIFICATION.md](VERIFICATION.md). The proof and axiom audit passed
locally; this artifact has not been accepted by the PEqualNP fleet.

## Explore the artifact

- [Download the packaged artifact and checksum](https://github.com/michaelhaislip/heawood-circuit-verification/releases/tag/v0.2.0)
- [Lean proofs and exact witness](lean/HeawoodBoundary.lean)
- [General star-cover adapters and examples](STAR_COVER.md)
- [Circuit and boundary data](data/heawood.json)
- [Verification instructions and search limitations](VERIFICATION.md)
- [Prior art and novelty assessment](RELATED_WORK.md)
- [Fleet contribution investigation](FLEET.md)
- [Privacy and publication scan](PUBLICATION_REVIEW.md)

The boundary principle and star-cover construction are established methods;
no mathematical novelty, optimality, or priority is claimed. This is a
supporting formalization, not a resolution of the lower-bound problem.

Version 0.2.0 reuses the upstream general star-cover formalization, adds
`Monotone2` adapters and examples, and recovers a 27-gate Heawood construction.
The general construction was already formalized upstream; our earlier
assessment that it was missing was incorrect.

## Attribution and license

AI assistance was used to develop the Lean formalization, computational
experiments, verification scripts, and documentation. The correctness
claims rest on the recorded Lean kernel checks and reproducible computation,
not on the AI's assertions. No independent human mathematical review is
claimed.

The circuit model and monotonicity helper proof pattern derive from
[brilliant-hq/pequalnp-proofs](https://github.com/brilliant-hq/pequalnp-proofs),
including `Outside/L_meta_616.lean`, at the pinned revision in
[PROVENANCE.json](PROVENANCE.json). Original upstream files are retained
under `upstream/`. See [RELATED_WORK.md](RELATED_WORK.md) for mathematical
attribution. Distributed under [Apache License 2.0](LICENSE).
