# autoresearch API

All functions are async and work only in the Eukhe Python kernel. Metric values are exact decimal strings (`"12.5"`). The host decides every outcome; a refused call raises with the reason and what to do.

## `await autoresearch.init(name, metric, *, goal=None, unit="", direction="lower", secondary=(), scope=(), off_limits=(), constraints=(), max_iterations=None, new_segment=False)`

Opens or reconfigures the session of this branch and turns the loop on.

- `metric`: the name in `METRIC <name>=<value>` (letters, digits, `_`, `.`, `-`).
- `direction`: `"lower"` or `"higher"` is better.
- `scope` / `off_limits`: paths (a directory covers what is below it). Changed paths outside `scope` or inside `off_limits` count as deviations.
- `constraints`: written to the notes under `## Constraints`.
- `max_iterations`: logged runs per segment; at the cap the loop stops.
- `new_segment=True`: a fresh baseline; needed to change the metric or the direction.

The first init needs `autoresearch.sh` in the repository root. Off an `autoresearch/*` branch it creates `autoresearch/<goal>-<YYYYMMDD>` (clean tree only); on it, it commits the harness changes. Returns `branch`, `git`, and the state fields below.

## `await autoresearch.run(timeout_s=600)`

Runs `bash autoresearch.sh` once in the repository root, through the same approval gate as `bash`. A run before the last one was logged is abandoned. Returns `run` (id), `passed` (exit 0, no timeout), `exit_code`, `timed_out`, `refused` (the gate's reason when it did not run), `metric` (`{name: value}`), `metrics` (secondary), `vs_baseline`, `vs_best` (percent), `baseline`, `best`, `tail` (last 10 lines, 4 KB), `log` (full output file).

## `await autoresearch.log(status, description, *, justification=None, flag_runs=())`

Logs the pending run. `status`: `"keep"`, `"discard"`, `"crash"`, `"checks_failed"`. `keep` commits with message `<description>` + `Result: {...}`; the others reset the tree to the last commit. Returns `run` (the row), `vs_baseline`, `baseline`, `best`, `confidence` (`Nx noise floor`), `git`, `deviations` (paths), `flagged`, `progress` (`n/max`), `stopped` (the cap was reached), `mode`.

`flag_runs`: `[{"run": n, "reason": "..."}]`, applied before the log.

## `await autoresearch.flag(run, reason)`

Marks run `run` as suspect: it leaves baseline, best and confidence, but still counts toward the cap. Returns the state.

## `await autoresearch.notes(body=None, idea=None)`

Returns the notes. `body` replaces them; `idea` adds `- idea` under `## Ideas`.

## `await autoresearch.state()`

Returns `mode` (`on`/`off`), `config`, `segment`, `pending` (a run that waits for its log), `baseline`, `best`, `best_vs_baseline`, `confidence`, `progress`, `runs` (the last 20 of the segment), `runs_in_segment`, `root`, `branch`, `harness` (whether `autoresearch.sh` exists), `store` (the session's directory), `notes`.

## Storage

`~/.eukhe/autoresearch/<repo>--<branch>/`: `events.jsonl` (every accepted event; replayed on open), `runs/NNNN/benchmark.log`, `notes.md`.
