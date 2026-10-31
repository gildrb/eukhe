---
name: autoresearch
description: Optimize a measurable property of code (speed, size, memory, score) in an autonomous loop that benchmarks every experiment and keeps only measured improvements. Use when the user runs /autoresearch, or asks to optimize, benchmark, or tune code toward a metric over many iterations.
---

# Autoresearch

Call from the Python REPL. API: [references/api.md](references/api.md).

## Set up the harness

1. Read the target. Decide what to measure and on which workload.
2. Write `autoresearch.sh` in the repository root. It MUST exit 0 on success and non-zero on failure, run the same workload each time (fixed seeds, no network, no clock), and print `METRIC <name>=<value>` for the primary metric (more lines for secondary metrics).
3. Validate it with `bash autoresearch.sh` until it exits 0 and prints the metric.
4. `await autoresearch.init(name, metric, goal=..., direction="lower", scope=[...])`. Off an `autoresearch/*` branch the tree must be clean.

## Loop

1. Baseline first: `await autoresearch.run()`, then `await autoresearch.log("keep", "baseline")`.
2. One coherent experiment per iteration: change the code, `await autoresearch.run()`, then log it before the next run.
3. Status: `keep` only when it improves (the host refuses other keeps and says why; it commits a keep), `discard` when it is flat or worse, `crash` when the run failed, `checks_failed` when it passed but your checks failed. Every status but `keep` resets the tree.
4. Confidence below 2x noise floor: run the change again before you keep it.
5. Record what you learn and what to try: `await autoresearch.notes(idea="...")`.
6. After a context reset, `await autoresearch.state()` is the truth: goal, runs, best, pending run, notes.

## Rules

- NEVER game the benchmark or overfit to its workload. Preserve correctness.
- NEVER edit `autoresearch.sh` mid-segment. To change it, the metric or the direction: `init(..., new_segment=True)`, then a new baseline.
- Stay in scope. A keep that changes paths outside `scope` needs `justification=`.
- A run that looks wrong (reward-hacked, broken workload): `flag_runs=[{"run": n, "reason": "..."}]` on the next log.
- Stop when `state()["mode"]` is `off` (the iteration cap, `/autoresearch off`, or a branch change) and report the best result.
