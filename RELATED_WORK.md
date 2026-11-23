# Existing results and novelty assessment

Reviewed on 2026-11-23. No mathematical novelty is claimed.

**Correction in v0.2.0:** the upstream project already formalized the general
star-cover construction at our original pinned revision. The initial search
missed `MetaComplexity/Helpers/CoverCircuitList.lean`, `CoverCircuitGraph.lean`,
and `EdgeUpperMono.lean`. These provide the explicit builder, correctness,
upper bounds, and exact construction-size results. Our new
`lean/StarCover.lean` reuses them as a compatibility layer and worked examples;
it does not supply a previously missing general construction. See
[STAR_COVER.md](STAR_COVER.md) for exact source links and theorem attribution.

1. The generic boundary principle is standard monotone Boolean-function
   theory. Bioch and Ibaraki, *Complexity of Identification and Dualization
   of Positive Boolean Functions*, Information and Computation 123 (1995),
   50–63, studies identification from minimal true and maximal false points:
   https://repub.eur.nl/pub/55247/1-s2.0-S0890540185711571-main.pdf
   Another primary source is Makino and Ibaraki, *The Maximum Latency and
   Identification of Positive Boolean Functions* (1994):
   https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/0871-12.pdf
   Our contribution is an explicit Lean implementation for this circuit
   semantics and graph, not discovery of the mathematical boundary fact.

2. The vertex-cover/star circuit construction is already explicit in
   Stasys Jukna, *Disproving the Single Level Conjecture*, equation (1.2):
   https://web.vu.lt/mif/s.jukna/ftp/single1.pdf
   Substituting the seven-vertex side of this bipartite cubic graph gives
   the 27-gate construction. Thus the upper-bound method is not new.
   That paper also shows why single-level restrictions cannot simply be
   assumed for arbitrary monotone circuits in general.

3. The fleet itself already calls this the least-cover circuit in the
   context of L-meta-971. Its posted gap says a checked lower bound is 21,
   while 27 remains open; L-meta-582 asks for a witness with at most 26.
   Public snapshot: https://data.pequalnp.com/data/desk/gaps.json
   The reviewed snapshot was updated 2026-11-23T20:01:22.018Z.
   These observations rule out claiming that we discovered the upper bound.

4. GitHub exact PR search for `"L-meta-971"` and a separate `Heawood`
   search returned no matches at review time. Public main source was
   searched for `heawood`, `boundary_check`, `maximal.false`, and
   `minimal.true`; no matching proof source was found. The pinned local
   tree was also searched. This is a limited text search, not a proof that
   an equivalent theorem under another name or graph labeling is absent.
   Additional exact-string searches for the initial three edges in this
   labeling and for `bitPoint 16256` also returned no matches.
   The source snapshot searched after fetching main was recorded separately
   in `upstream/review-source-revision.txt`.

Web queries included `Heawood graph monotone circuit complexity 27`,
`"Heawood" "27" "circuit"`, and `"Heawood" "monotone" "Lean"`.
No exact earlier formalization of this witness and boundary list was
identified. Search coverage is incomplete; formalization novelty remains
unestablished. No priority or first-formalization claim is made.
