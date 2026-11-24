# Equal-budget portfolio experiment

AI-assisted computational research, 2026-11-23. This experiment compares
search policies; it establishes no new circuit lower bound or Lean theorem.

## Predeclared protocol

Seven-cycle edge function, nine and ten gates, normalization enabled.
Ten gates has a separately constructed witness checked on all 128 inputs;
the nine-gate answer is not independently established here. Five held-out
base seeds are 100, 102, 104, 106, and 108 (not the pilot seeds 0, 1, 2).

- Single: original nested-conditional encoding at the base seed, 12 seconds.
- Portfolio: original/base, implication/base, original/base+1,
  implication/base+1, each with a three-second limit; stop on SAT or UNSAT.

The total configured solver budget is 12 seconds per strategy trial.
Solver timeout cleanup can slightly overrun the limit. Setup, verification,
and process startup are outside that budget and included in end-to-end time.
Early success leaves unused time. Runs are sequential in fresh processes,
with a fixed shuffled strategy schedule (seed 20261125). No strategy was
changed after seeing these results. These are five paired seeds on one graph,
not ten independent graph instances. No parallel speedup is being measured.

## Results

Counts are SAT/UNSAT/timeout. Medians include timeouts as observed capped
times, not as completed runtimes. Do not infer a runtime beyond the cap.

| Gates | Strategy | Counts | Median solver s | Median end-to-end s |
| ---: | --- | --- | ---: | ---: |
| 9 | single | 0/0/5 | 12.019 | 12.346 |
| 9 | portfolio | 0/0/5 | 12.063 | 13.444 |
| 10 | single | 5/0/0 | 2.456 | 2.813 |
| 10 | portfolio | 5/0/0 | 2.491 | 3.010 |

| Gates | Base seed | Single outcome, wall time | Portfolio outcome, wall time | Portfolio attempts |
| ---: | ---: | --- | --- | ---: |
| 9 | 100 | unknown, 12.345s | unknown, 13.359s | 4 |
| 9 | 102 | unknown, 12.359s | unknown, 13.497s | 4 |
| 9 | 104 | unknown, 12.360s | unknown, 13.765s | 4 |
| 9 | 106 | unknown, 12.346s | unknown, 13.329s | 4 |
| 9 | 108 | unknown, 12.334s | unknown, 13.444s | 4 |
| 10 | 100 | sat, 10.639s | sat, 4.719s | 2 |
| 10 | 102 | sat, 2.813s | sat, 2.906s | 1 |
| 10 | 104 | sat, 0.927s | sat, 1.041s | 1 |
| 10 | 106 | sat, 3.999s | sat, 4.930s | 2 |
| 10 | 108 | sat, 2.745s | sat, 3.010s | 1 |

## What the comparison supports

Both strategies solve all five ten-gate cases and none of the five
nine-gate cases. The portfolio improves the slow base-seed-100 trial
(10.639 to 4.719 seconds end-to-end), but is slower on the other four
ten-gate pairs. Its mean end-to-end time on these five completed SAT cases
is 3.321 seconds versus 4.225 for the single run;
its median is slightly worse (3.010 versus 2.813 seconds). The mean advantage
is driven by one slow single-run trial, not a consistent per-pair win.

On nine gates both strategies use the full configured solver budget and
remain inconclusive. The portfolio incurs additional repeated setup/startup
costs, with median end-to-end time 13.444 versus 12.346 seconds. These
measurements support a possible tail-latency benefit on satisfiable cases,
not a demonstrated general improvement in search effectiveness. Do not
replace the baseline or scale this portfolio to Heawood on this evidence
alone; evaluate a broader predeclared family before making that choice.


## Interpretation limits

The portfolio reuses the single strategy's first seed with a shorter cap;
it is a paired comparison, not independent sampling. A three-second cutoff
can discard a run that would finish within twelve seconds. Different seeds
can recover that loss, but this experiment does not guarantee that they do.
Compare both completion counts and end-to-end costs, not just successful
run averages. The narrow graph family, small sample, fixed ordering inside
the portfolio, machine load, and pilot-informed protocol limit generalization.
No result here establishes that either policy is better for Heawood.

Every SAT attempt is checked on the full truth table by the solver wrapper.
Any UNSAT is an uncertified result for the encoded model; normalization
completeness and solver refutations have not been checked in Lean. Timeouts
remain inconclusive. The original six Heawood timeouts are unchanged.

## Reproduce

Python 3.10+, with a virtual environment and the pinned Z3 requirement:

```text
python -m pip install -r requirements.txt
python -u portfolio_benchmark.py --output portfolio-results.jsonl
python audit_results.py
```

Do not use Python -O. Expect up to roughly four minutes of configured solver
time plus process/setup costs. The raw output includes the protocol before
the first trial, environment versions, witnesses, each attempt's statistics,
and strategy-level timings. Timings and completions may vary across machines.

Source derives from the AI-assisted diagnostics for
https://github.com/michaelhaislip/heawood-circuit-verification
Apache-2.0; see LICENSE. This follow-up is included in release v0.3.0 and has not been submitted to the fleet.
