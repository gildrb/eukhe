# Dynamic workflows

One JavaScript orchestration script the agent writes and eukhe runs: starts many subagents at once (up to the size), waits, returns one result; eukhe shows progress.

## Use

```
/dynamic-workflow review every crate for unsafe error handling   # default size
/dynamic-workflow --size large migrate the tests to the new API     # one run, size large
/workflows size                                                     # size picker
/workflows size small                                               # set the default size
/workflows                                                          # this session's runs
```

- `/workflow` = `/dynamic-workflow`. `--size` comes first; after `--size ` the menu lists the sizes.
- Runs in the background; chat goes on. The `workflow` call returns the run id at once.
- Result arrives as `[job-settled job:workflow-<id> status:ok|error|aborted]`, which starts an agent turn.
- `/workflows`: arrows move, Enter opens the agents view, `c` then `y` cancels, Esc closes.
- Chat Esc stops the turn, not the run; cancel on `/workflows`.
- While running: activity dock shows a `workflows` count (Enter opens `/workflows`); the agents block above the composer shows the run (active phase, agents done) and each running agent (`terminal.pinnedAgents`, [settings.md](settings.md)).
- Signal gateway and dashboard send `/dynamic-workflow` as a prompt.

## Sizes

|Size|Agents at once|Agents in total|
|---|---|---|
|`small`|3|5|
|`medium`|6|10|
|`large`|12|25|

- Setting `workflow.size`, default `medium`.
- `subagentMaxConcurrency` caps agents at once; 0 = no cap.
- `agent()` past the total throws `WorkflowBudgetExhausted`; in `parallel`/`pipeline` that slot is `null`.

## Script API

Body of an async function; starts with a pure literal meta:

```js
export const meta = { name: "review", description: "Review the changed files", phases: [{ title: "Scan" }, { title: "Fix" }] };
```

|Global|Effect|
|---|---|
|`agent(prompt, opts?)`|One subagent → final message, parsed object for `schema`, or `null` on failure|
|`parallel(thunks)`|Runs `() => agent(...)` thunks at once, waits for all; a throw → `null`|
|`pipeline(items, ...stages)`|Each item through the stages in order, no waiting between items; `null` stops an item|
|`phase(title)`|Enter a `meta.phases` phase|
|`log(message)`|Line in the run log|
|`args`|Request text|
|`budget`|`{ size, concurrency, maxAgents, spawned() }`|

|`agent()` option|Effect|
|---|---|
|`label`|Name on `/workflows`|
|`phase`|Phase; default the last `phase()`|
|`schema`|JSON Schema; agent ends with a matching JSON block; mismatch: one retry, then `null`|
|`model`|Model|
|`effort`|Thinking level|
|`isolation`|`"worktree"`: copy-on-write workspace copy; changes return at the end|

- `Date` virtual, `Math.random` seeded, no I/O.
- Agents do not see the conversation: put every fact in the prompt.
- The return value goes into the result message: keep it small.

## Resume

- Worker restart resumes: finished agents from the journal, running agents reattach, a cut-off agent runs once more; one result message.
- Start answer and result name the run: `workflow run <id> (<name>)`.
- `resume: "<id>"` on a new run reuses finished agents with unchanged prompt and options; shown `↺`, not counted against the total.

## Limits

- Needs the daemon; `--no-session` refuses the tool.
- Agents are subagents: `rlmMaxDepth` limits depth.
- Agents report to the script, not the conversation.
- Dashboard shows runs, cannot cancel.

## Autoresearch

An experiment loop toward a goal (port of omp autoresearch): the agent builds a benchmark harness, measures each experiment with it, and keeps only the improvements. The compiled Lab (Bend, entry 430) makes every decision; the host runs the harness, keeps the log and does git.

### Use

```
/autoresearch make the JSON parser faster   # branch, mode on, loop starts
/autoresearch status                         # or /autoresearch alone
/autoresearch off                            # mode off, loop stops
/autoresearch clear                          # mode off, session of this branch closed
```

|Command|Effect|
|---|---|
|`/autoresearch <goal>`|Puts the repository on `autoresearch/<slug(goal)≤48>-<YYYYMMDD>[-N]` (kept when already on an `autoresearch/*` branch; a dirty tree is an error; no git: a warning, no branch, commits or resets). Turns the mode on, starts the loop, sends a turn: set up the harness (no session yet) or resume (session open; the goal text is extra context).|
|`/autoresearch status`|Mode, metric, segment, runs logged / cap, baseline, best, pending run.|
|`/autoresearch off`|Mode off; the loop stops.|
|`/autoresearch clear`|Mode off; the store moves to `<store>.cleared-<ms>` (kept); the next init opens a new session. Tree and branch stay.|

### Skill API

Bundled Python skill `autoresearch` (`skills/autoresearch`; reference `references/api.md`). Host requests `autoresearch.init`, `.run`, `.log`, `.flag`, `.notes`, `.state` (`crates/eukhe-core/src/autoresearch/host.rs`).

|Call|Effect|
|---|---|
|`init(name, metric, *, goal, unit, direction, secondary, scope, off_limits, constraints, max_iterations, new_segment)`|Event `Init`. Off an `autoresearch/*` branch: creates it first (clean tree only). On it: an accepted init commits the harness changes (`autoresearch: harness`). `constraints` go to the notes (`## Constraints`).|
|`run(timeout_s=600)`|Events `Start`, `Line` per output line, `Finish`. Runs `bash autoresearch.sh` in the repository root. Output: `runs/NNNN/benchmark.log`. Reply: passed, exit code, metrics, last 10 lines (4 KB), baseline, best.|
|`log(status, description, *, justification, flag_runs)`|Events `Flag` per entry, then `Log`. Lab answer `Commit`: `git add -A`, commit `<description>\n\nResult: {"status":"keep","<metric>":<value>}`. `Reset`: `git reset --hard HEAD`, `git clean -fd` (only on an `autoresearch/*` branch). Reply: row, delta vs baseline (%), best, confidence (`Nx noise floor`), git note, progress `n/max`, stopped.|
|`flag(run, reason)`|Event `Flag`.|
|`notes(body, idea)`|`notes.md` in the store: `body` replaces, `idea` adds a bullet under `## Ideas`. No event.|
|`state()`|Snapshot of the Lab, notes, branch, store directory.|

- The host computes only inputs: the run id (1 + runs started), the exit code (timeout: 124, `timed_out`), the scope deviations (changed paths outside `scope` or inside `off_limits`; a directory covers what is below it).
- A Lab refusal raises in Python with the Lab's text; state and log stay unchanged.
- Metric values are exact decimals (text); the skill formats deltas and confidence.

### Gate

- The run is one `bash` step: the in-process shell of the `bash` tool, with `shell.autoEffects`, the session path policy and the approval sink. `exec` outside the auto set: the user is asked (request id `autoresearch:<call>:<step>`); a refusal leaves the run unfinished (the next run abandons it).
- Timeout kills the script and every process it started.
- Git commands run with the untrusted-repository arguments (no hooks, fsmonitor, pager).

### Store

|Path (under `~/.eukhe/autoresearch/<repo-key>/`)|Content|
|---|---|
|`events.jsonl`|Every event the Lab accepted, one JSON line, in order|
|`runs/NNNN/benchmark.log`|Output of run `NNNN` (stdout and stderr)|
|`notes.md`|Notes, ideas, constraints|

- `<repo-key>`: repository root with `/` → `-`, then `--<branch>` (`/` → `-`; `HEAD` detached; `nogit` without git). One session per repository branch.
- Write-ahead: an accepted event is appended before its effect runs; events with an effect are fsynced first (output lines are synced with the next `Finish`).
- Open replays the log through a fresh Lab. A last line without newline (crash during the write) is cut off. A refused or undecodable line is an error (corrupt log).
- One lock per store in a process: one operation at a time per branch. A log that another process grew is replayed again.

### Loop

- The loop is the autonomous run of the Director stack ([control.md](control.md) S5), prompt `autoresearch` continuation (call `state()` first, log a pending run, next experiment). No second loop.
- Starts when the Lab's mode turns on (`/autoresearch <goal>`, an accepted init) and no autonomous run is on. A user's own autonomous run is never changed.
- Stops when an operation finds the mode off: the cap (`max_iterations` logs in the segment), `/autoresearch off`, `/autoresearch clear`, or a branch change (the new branch has its own store, mode off).
- Its own limits (continuations, turns, tokens, timeout) are 2^53 − 1, the largest integer exact JSON holds (the run's state is a durable document): never reached first. `directors.maxSteps` still caps one run's continuations.
- After a context reset or a restart: state from the event log (`state()`).

### Lab

The rules of the Lab (`bend/autoresearch/`, stepper `bend/ffi_autoresearch.bend`, Rust `eukhe_bend::rules::autoresearch::Lab`). A refusal changes nothing; its text tells the model what to do.

|Event|Accepted when|Then|
|---|---|---|
|`Init`|Metric name is 1+ of `A-Z a-z 0-9 _ . -`; `max_iterations` ≥ 1 (or none); a first init or `new_segment` needs `harness`; an init on the same segment keeps metric and direction|Configuration set, mode On, pending run abandoned; `new_segment` on an existing experiment: segment + 1 (first init: segment 0)|
|`Start{run}`|An experiment exists; `run` = 1 + runs started|Pending run abandoned (row without status); new pending run, no metrics|
|`Line{text}`|A run is running|A `METRIC <name>=<value>` line sets that metric (last value wins); any other line changes nothing|
|`Finish{exit_code, timed_out}`|A run is running|Run finished; passed = exit 0 and not timed out|
|`Log{status, ..}`|The pending run finished. `keep`: passed, printed the primary metric, metric strictly better (direction) than every kept, unflagged run of the segment, `deviations` > 0 needs a justification. `crash`: not passed. `checks_failed`: passed. `discard`: always|Row appended with the parsed metric (never a model value); keep → `Commit`, others → `Reset`; logged runs of the segment ≥ cap → `stopped`, mode Off|
|`Flag{run, reason}`|`reason` not empty; `run` is a logged run (any segment)|Run flagged (stays flagged)|
|`SetMode`|Always|Mode set|

- METRIC line: `METRIC`, 1+ spaces or tabs, name, `=`, `[-]D+[.D+]`, optional trailing spaces, tabs, CR. At most 15 significant digits. Anything else (`1.`, `.5`, `1e3`, text after the value) is not a metric.
- Metric: exact decimal (sign, digits, scale), canonical (`-0012.500` is `-12.5`). Order by value, not text.
- Baseline: first kept, unflagged run of the segment. Best: last such run (each keep beats all before it). Logged in segment: flagged runs count.
- Confidence (tenths, rounded down, at most 999999999): |best − baseline| / MAD over the segment's logged, unflagged metrics. None below 3 metrics, without baseline, with best = baseline, or with MAD 0. Exact arithmetic (no floats).

### Laws

`laws/autoresearch/{model,history,entry}.bend`; specs `spec/autoresearch/{decimal,metric_line,segment,stats}.bend`; proofs `proof/autoresearch/`.

|Law|Claim (bug class it excludes)|
|---|---|
|`metric_order_exact`|Order of well-formed decimals = order of their values by arithmetic (text order, scale, sign, -0)|
|`metric_order_reverse`, `metric_order_self`|Order is antisymmetric and reflexive (a keep that beats the best while the best beats it)|
|`metric_line_reads`|Every grammar line means its name and a canonical decimal of the written value; nothing past 15 digits (misread value, lost name, valid line ignored)|
|`metric_line_sound`|Only grammar lines give a metric (garbage read as a metric)|
|`metric_print_round_trip`|Printed canonical metric reads back as itself (printer/parser drift)|
|`metric_last_wins`|A METRIC line sets its name, keeps the others (first value kept, value lost)|
|`line_sets_metric`, `finish_marks_passed`, `output_needs_run`|Output and end of a running run; nothing for an idle one (timeout marked passed, output into a logged run)|
|`keep_needs_pass`, `crash_needs_failure`, `checks_need_pass`|Status matches the outcome (failed run kept, passing run logged as crash)|
|`log_needs_pending`|Log without a finished run is refused with the exact text|
|`keep_is_better`|Accepted keep beats every kept, unflagged run of the segment (tie or loss kept, wrong direction, flagged or other segment counted)|
|`keep_needs_justification`|Out-of-scope keep needs a justification|
|`log_records`|Logged row has the parsed metric; no pending run after (model-supplied metric)|
|`effect_matches_status`|Keep commits, other logs reset, other events touch nothing|
|`cap_stops`|Stop exactly at the cap; mode Off on stop, On on init, set by `SetMode`, else kept|
|`start_abandons`|Next id; one pending run; old pending run abandoned (two pending runs, reused id)|
|`init_needs_harness`, `init_sets`, `init_keeps_metric`|Harness first; valid name and cap; same segment keeps metric and direction|
|`segment_monotone`|Segment moves only by +1 on a new-segment init|
|`flag_monotone`, `flag_marks`|Flags stay; a flag needs a reason and a logged run|
|`flagged_excluded`|Baseline, best, confidence ignore flagged runs|
|`confidence_none_below_3`, `confidence_exact`|Confidence = spec MAD formula; none below 3 metrics (median, sign, scale, rounding, overflow)|
|`run_conservation`|Runs are ids 1..n for n accepted starts; n = logged + abandoned + pending|
|`best_is_best`|Best: no kept, unflagged run of the segment is better; none iff nothing kept|
|`best_never_worse`|In a segment, only a flag can make the best worse|
|`autoresearch_entry_answers`, `autoresearch_entry_exact`|Each spelled request answers as the model; any other input answers exactly `E autoresearch: malformed request` and keeps the state|
|`autoresearch_step_is_model`|Stepper after any requests = fold of the model (replay rebuilds the state)|
|`autoresearch_entry_open`, `autoresearch_entry_open_malformed_exact`, `autoresearch_entry_shut`|Open with no input is the empty state; any input is refused|
|`metric_order_example`, `metric_line_example`, `autoresearch_example`, `autoresearch_entry_example`|Anchors|
