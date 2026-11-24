# Intermediate circuit-search benchmark

AI-assisted computational experiment, 2026-11-23. No new Lean theorem,
general circuit lower bound, or fleet acceptance is claimed.

## Design

The main suite compares nested-conditional wire selection (`ite`) against
guarded-equality selection (`implication`) on three disjoint edges and cycles
of lengths 5, 6, and 7. Each graph is tested at the independently verified
star-cover upper bound and one gate below it, with seeds 0, 1, and 2. Both
encodings receive five seconds per solver call. Every run uses a fresh
process; jobs are interleaved in a fixed shuffled order (schedule seed
20261123), executed sequentially. Normalization is enabled in the main suite.
The ablation repeats the six-cycle jobs without normalization, with a
separate fixed shuffled schedule (20261124). Total: 48 + 12 = 60 runs.

The metadata records Python/Z3 versions and explicit upper-bound witnesses.
Those witnesses and every synthesized SAT witness are checked on the full
truth table. The matching minimum is independently known to be 5: all six
inputs are essential, so at least five binary gates are necessary, and the
stored witness has five gates. The cycle lower bounds are not independently
established by this experiment. UNSAT outcomes are solver verdicts for the
encoded model, without proof certificates or a Lean proof of normalization.

## Main comparison

Cells show **SAT/UNSAT/timeout counts; median observed solver wall time**.
Each cell contains three seeds. Timeout observations are censored at roughly
five seconds; their recorded time is not a completed solution runtime.

| Graph | Gate budget | ite | implication |
| --- | ---: | --- | --- |
| matching3 | 4 | 0/3/0; 0.032 s | 0/3/0; 0.032 s |
| matching3 | 5 | 3/0/0; 0.050 s | 3/0/0; 0.029 s |
| cycle5 | 6 | 0/3/0; 0.244 s | 0/3/0; 0.191 s |
| cycle5 | 7 | 3/0/0; 0.136 s | 3/0/0; 0.181 s |
| cycle6 | 7 | 0/3/0; 2.394 s | 0/3/0; 1.550 s |
| cycle6 | 8 | 3/0/0; 0.339 s | 3/0/0; 0.719 s |
| cycle7 | 9 | 0/0/3; 5.016 s | 0/0/3; 5.020 s |
| cycle7 | 10 | 2/0/1; 1.845 s | 2/0/1; 3.187 s |

Both encodings complete 20 of 24 main-suite calls. Each times out for all
three seeds on the nine-gate seven-cycle case, and for one seed on its
ten-gate case. Thus this experiment identifies no overall completion-rate
winner. The failing ten-gate seed differs between encodings: seed 0 for
ite and seed 2 for implication. A timed-out satisfiable case is a direct
demonstration that failure to find a circuit need not mean nonexistence.

On the six-cycle, implication has the lower median for the seven-gate
UNSAT case, while ite has the lower median for eight-gate synthesis. This
supports an instance-dependent choice, not a universal speed ranking.
Three seeds, one machine, and this narrow graph family limit generalization.
These intermediate runs cannot by themselves explain every earlier Heawood
timeout or show which encoding is better on Heawood.

## Normalization ablation (six-cycle)

| Gate budget | Normalization | ite | implication |
| --- | --- | --- | --- |
| 7 | True | 0/3/0; 2.394 s | 0/3/0; 1.550 s |
| 7 | False | 0/0/3; 5.013 s | 0/0/3; 5.011 s |
| 8 | True | 3/0/0; 0.339 s | 3/0/0; 0.719 s |
| 8 | False | 1/0/2; 5.025 s | 3/0/0; 1.571 s |

All 12 normalized six-cycle calls completed within the limit, versus only
4 of 12 unnormalized calls. Every unnormalized seven-gate call timed out;
normalized calls returned UNSAT in 1.3 to 2.8 seconds. At eight gates,
normalization removed the two observed ite timeouts. This is the clearest
performance effect measured here, subject to the normalization soundness
and restricted-family limitations already stated.

The ablation toggles the normalization bundle, not individual constraints.
That bundle includes alias/constant elimination, an active prefix with copy
padding, adjacent ordering, live-use requirements, and all-input-use
constraints. It does not isolate the contribution of each rule. Normalized
and unnormalized records must be consulted before drawing timing conclusions.
Solver time includes preprocessing and search; these phase shares remain
unmeasured. No percentage of proof completion is inferred from statistics.

## Next step

Retain both encodings and the normalization bundle rather than declaring a
winner. The seven-cycle at ten gates is a useful known-satisfiable regression
case for seed/encoding sensitivity. Any further experiment should predeclare
equal total compute budgets for a portfolio versus a single longer run.
Before interpreting encoded UNSAT as a theorem, independently validate or
formalize the normalization and obtain a checkable proof certificate.

## Reproduction

Use Python 3.10+ in a virtual environment; do not use -O (assertions check
results). Install the pinned requirement and run the suites sequentially:

```text
python -m pip install -r requirements.txt
python -u intermediate_benchmark.py --timeout 5 --output intermediate-results.jsonl
python -u normalization_ablation.py --output normalization-ablation.jsonl
python audit_results.py
```

Each raw record includes seed, encoding, normalization, build/serialization/
solver times, CPU time, solver statistics, formula hash, and the full-table
checked witness when SAT. Timings and outcomes can vary by machine and load.
Five seconds is a solver limit, not the entire process budget. The worker
watchdog allows extra startup time and is not a mathematical resource bound.

The scripts extend the AI-assisted Heawood diagnostic encoding; source
attribution: https://github.com/michaelhaislip/heawood-circuit-verification
Apache-2.0; see LICENSE. This package is included in release v0.3.0 and has not been submitted to the fleet.
