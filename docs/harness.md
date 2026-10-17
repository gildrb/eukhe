# Harness laws

This page is the spec of the harness's liveness. Each rule says what must
always happen, whatever the model, the provider, or the timing does. Each
rule has a model in Bend, a law in `LAWS.bend`, a proof in `PROOF.bend`,
and a tie to the Rust code: a bridge test (the Rust code and the Bend model
run the same scenarios and must print the same output) or a regression test.

Paths start at `crates/`.

## What a law secures, and what it does not

- A law is proven for the Bend model, for every input it names.
- A bridge test shows that the Rust code makes the same steps as the model
  on its scenarios. The scenarios are finite.
- A deadline in Rust (a timer, a fuel count) is what makes a wait end in
  production. The law shows that the deadline is enough: no state is left
  where nothing more happens.
- No law covers the compiler, the operating system, or the network.

## The adversary

The laws treat these as free inputs. Any value, in any order:

- the model's reply: text of any length, empty text, thinking only, an
  error, no reply until the deadline;
- the provider: up, slow, down, rate limited, auth expired;
- the timing: which event comes first, how many ticks pass;
- the user: a new message, an abort, at any time.

## Rules

### H1. A compactor call always ends with a line that fits

A compactor call builds one line of the chat memory (a message summary or
a merge of two lines).

1. It asks the model at most `TRIES` times.
2. It stops early when a follow-up reply is not shorter than the best one.
3. It returns a line of 1 to `NODE` bytes. If no reply fits, it cuts the
   shortest reply (or, with no reply, the input) to `NODE` bytes at a
   character boundary.
4. An empty reply or a thinking-only reply counts as a try, never as a
   failure of the call. It ends the tries: asking again asks the same.
5. A provider error, or a model call past `CALL_DEADLINE` (10 min, the
   wait for a provider slot and every preemption by a session request
   included), fails the call. After `FAILURES` (3) failed calls of a node,
   the node is built from its input, cut to `NODE` bytes. The cut needs
   no read: the input is the one the failed call had. Only its save can
   fail, and a failure of the disk (a read of a node's input, a save of a
   line or of the input cut) counts no failure: the node stays as it was.

Model: `line`, and `Pend.after` with its fold `Pend.run`, in
`bend/compactor.bend`. Proofs: `bend/proof_compactor.bend`. Every law is
universal: for every input, every list of replies, every number of
tries, every sequence of a node's call outcomes.

| Law | Says |
| --- | --- |
| `line_calls_at_most_tries` | A line makes at most `tries` model calls (H1.1). |
| `line_stops_when_not_shorter` | A follow-up not shorter than an over-long reply ends the line after 2 calls, with that reply cut to `NODE` bytes (H1.2). |
| `line_fits` | With an input that is not empty and `NODE` of at least 4 bytes (the widest character), the line has 1 to `NODE` bytes, or the call failed (H1.3). |
| `line_takes_first_fit` | When a reply the line read fits, the line is the first such reply (H1.3). |
| `line_empty_is_a_try` | An empty (or thinking-only) reply ends the line with the input cut to `NODE` bytes (H1.4). |
| `line_error_fails` | A provider error fails the call (H1.5). |
| `fail_cap_builds` | A node with n failures left is built once n+1 of its calls failed, whatever came between them: disk errors, stops, a saved line (H1.5). |

Code: `eukhe-core/src/memory/compactor.rs` `build_line` (the loop,
`CALL_DEADLINE` on each model call), `Pend::after` (the count);
`memory/mod.rs` `TRIES`, `FAILURES`, `CALL_DEADLINE`, `cut`;
`memory/service/actor.rs` `Actor::failed` (counts with `Pend::after`;
the failure with none left saves the input cut), `Command::Built` (the
call hands its input back), `Actor::source` (a node's input).

Tie: the bridge test `memory::compactor::bridge::the_compactor_equals_the_bend_model`
runs `build_line` on a scripted model and `bend/bridge_compactor.bend` on
2,000 generated scenarios (inputs and replies of 1 to 3,000 bytes, 1- to
4-byte characters across the cut, empty and thinking-only replies, text
split in blocks or padded with spaces, errors, too few replies) and
compares the calls made and the line, byte for byte. It also runs every
sequence of up to six failed calls and disk errors through
`Pend::after` and the model's `Pend.after` and compares the failures
left after each. Regression tests:
`compactor::tests::failed_replies_fail_and_empty_ones_give_the_input_cut`,
`a_follow_up_not_shorter_ends_the_tries`,
`over_long_lines_get_the_cut_and_the_shortest_cut_wins`,
`a_model_call_past_its_deadline_fails`,
`service::tests::a_node_that_keeps_failing_is_built_from_its_input`,
`an_empty_reply_still_gives_a_line_that_fits`,
`the_failure_cap_reads_nothing` (the log moved away before the last
failure: the node is still built from its input; fails with a cap that
reads the message again).

### H2. A turn never waits forever for the memory

A turn waits until every line before its message is summarized (gist rule
47).

1. While a turn waits, the compactor builds the lines that the turn needs
   first: a node in the view that is not built goes before any other node.
   When a turn starts to wait, every running call of a node it does not
   need stops (no failure: the node goes back to the queue), so a merge
   never holds a one-request provider while the turn waits. No call of a
   line the view needs is ever stopped, and the queue starts one whenever
   a job slot is free and such a line has no call.
2. Every pending node is built after a bounded number of counted
   outcomes of its calls: a saved line, or a failed call (H1.5). So the
   wait ends.
3. A deadline (`memory.settleTimeoutMs`, default 20 s; `0` or unset
   takes the default) is the last guard.
   When it fires, the turn goes on with the view as it is: a line not
   built yet shows its input, cut to `NODE` bytes. The wait never ends
   with an error.

Model: the need-first queue `cands.need` and the stop `St.wait` in
`bend/optchat.bend`; the settle in `bend/compactor.bend`: each view line
is built (`Made`) or pending with the failures it has left (`Owed{n}`),
and the measure is the sum of `n + 1` over the pending lines. A call of
a pending line ends `Built` (its line saved), `Failed`, `Disk` (the disk
failed) or `Stopped` (a waiting turn stopped it); only the first two
count. Proofs: `bend/proof_compactor.bend`. Every law is universal;
`need_progress` holds after any events from an empty chat.

| Law | Says |
| --- | --- |
| `need_first` | While a turn waits, every node the queue starts is a line of the view that is not built (H2.1). |
| `need_first_running` | Once a turn starts to wait (`St.wait`), every running call and every call the queue starts is for a line of the view that is not built (H2.1). |
| `wait_keeps_needed` | `St.wait` stops no call of a line of the view that is not built (H2.1). |
| `need_progress` | After any events, while fewer than `jobs` calls run and a view line is neither built nor busy, the queue starts a node (H2.1). |
| `settle_falls` | Each counted outcome (built or failed) of a pending line's call lowers the measure (H2.2). |
| `settle_bounded` | After any outcomes, in any order, of calls of any line, disk errors and stops among them, the counted outcomes that hit a pending line plus the measure left are at most the measure at the start (H2.2). |
| `settle_reached` | So once as many counted outcomes as the measure hit pending lines, every line of the view is built (H2.2). |
| `settle_start` | When a turn starts to wait, the measure is `FAILURES` times the view's unbuilt lines (H2.2). |

What bounds the wait:

- Outcomes. With `need_first_running`, every call that runs while a turn
  waits is a call of a pending line, and with `need_progress` such a call
  starts whenever a slot is free and a pending line has none (a failed
  line is busy until its retry). So after `FAILURES` times the unbuilt
  view lines counted outcomes the view settles.
- Stops. Every waiting turn waits for the same view, the current one, so
  by `wait_keeps_needed` no turn's wait stops a call that any waiting turn
  needs: stops never hit a pending line.
- Preemptions. A session request preempts a compactor request (H3.1);
  the call asks for a slot again and resumes. This happens inside one
  model call and is not an outcome: `CALL_DEADLINE` counts the waits and
  the preemptions, so a call preempted without end fails at it, a counted
  outcome. Each counted outcome thus comes within `TRIES` times
  `CALL_DEADLINE` of its call's start, plus `RETRY` before a failed
  line's next call.
- The disk. A disk that keeps failing keeps a line pending; no law covers
  the disk.
- Time. The bounds above are far longer than a turn waits: the settle
  deadline (H2.3) ends every wait, whatever the outcomes.

Code: `memory/chat.rs` `Demand`, `Chat::candidates` (with
`Demand::Turn`, the ready merges wait); `memory/service/actor.rs`
`Actor::pump` (the demand; waking the turns lets the held merges start),
`hold_for_turn` (`Chat::hold_for_turn`, then abort the calls, drop them
from the prefix gate; `Command::Built` and `Started` carry the call's
number, so a stopped call's result is ignored; a stop leaves the node's
failure count alone), `Actor::failed` (`Pend::after`),
`add_view_waiter` (the waiter's deadline), `Actor::run` (waits for the
next command at most until the first deadline, on the owner thread's
clock), `expire_waiters`, `deadline_view` (the view with each unbuilt line
as its input cut);
`memory/service.rs` `Memory::settled_render(within)`;
`memory/summarizer.rs` `SettingsSummarizer::complete` (a preempted request
asks for a slot again, inside the call's `CALL_DEADLINE`);
`settings/manager.rs` `get_memory_settle_timeout` (`memory/mod.rs`
`SETTLE_TIMEOUT`); `durable/optchat/request.rs` `pin`.

Tie: the memory bridge (`memory::chat::bridge`) prints, after every
event, the queue while a turn waits (`n=`): the Rust
`candidates(Demand::Turn)` against the model's `cands.need`, at every T
of every scenario; its lagging scenarios also start turns' waits (event
`6`: Rust `Chat::hold_for_turn` against `St.wait`). The compactor bridge
ties the failure count (H1). Regression tests:
`service::tests::a_waiting_turn_stops_a_merge_that_holds_the_slot` (the
incident: a one-slot provider, a merge call that never answers; fails
without the stop),
`a_turn_gets_the_view_by_its_deadline_when_the_model_never_answers`
(real time: the deadline runs on the owner thread),
`a_node_that_keeps_failing_is_built_from_its_input` and
`an_empty_reply_still_gives_a_line_that_fits` (tokio paused time). Not
modelled: the order in which the provider serves calls that already run
(H3).

### H3. A user's request never waits behind background work

1. A session request preempts every compactor request of its provider.
2. Requests of one class are granted oldest first.
3. When a slot is free and a request may take it, it takes it at once: no
   lost wake-up.
4. An interactive request waits only for interactive requests ahead of it.

Model: `bend/admission.bend`, one provider's admission, ticket by ticket.
The state is the limit, the queue limit, and one entry per ticket in
ticket order: its class and its status (`Queued`, `Granted` not yet
collected, `Held`, `Preempted`, `Ended`). The Rust queues are the queued
entries of a class in ticket order; the Rust counters are counts of
entries. The ops are an admit of either class, a waiter's poll, a
permit's drop, a waiter's drop, and new limits, each as the Rust code
does it (only a release or a drop calls the grant loop; an admit grants
only the new ticket). Proofs: `bend/proof_admission.bend`,
`bend/proof_admission_wait.bend` (H3.4). Every law is universal: the
step laws hold for any state and op, the history laws for every state
any ops reach from a new controller.

| Law | Says |
| --- | --- |
| `admission_preempts` | After an interactive admit no background slot is held (H3.1). |
| `admission_background_yields` | After any history, a background slot is held only while no interactive request holds a slot or waits (H3.1). |
| `admission_fifo` | After any history, no request holds a slot while an older one of its class waits (H3.2). |
| `admission_no_lost_wakeup` | After any history, no slot is free while an interactive request waits, or while a background one waits and no interactive request holds or waits (H3.3). |
| `admission_capacity` | An op grants only into free slots: after it the slots held are within the limit, or no more than before less the slots the op freed itself. A lowered limit drains; nothing is granted until the slots held are below it. |
| `admission_interactive_step` | While interactive ticket w waits, no op raises `ahead(s, w)` (the interactive slots held plus the interactive waiters older than w), and an op that frees an interactive slot (a release, or a granted waiter that leaves) lowers it by one (H3.4). |
| `admission_interactive_bound` | So while w keeps waiting through any run, the run freed fewer than `ahead(s, w)` interactive slots: w is granted after at most that many interactive releases, whatever background requests do (H3.4). |
| `admission_ended_stays_ended` | An ended ticket stays ended, whatever op comes. |
| `admission_end_twice_changes_nothing` | Ending an ended ticket again changes nothing: no double release. |
| `admission_every_ticket_ends` | Every ticket ends when its holder drops it (a waiter leaves, a permit is released): no leak. |

`admission_interactive_bound` rests on `admission_no_lost_wakeup`: while
w waits, `ahead(s, w)` is at least one, since with no interactive slot
held and no older interactive waiter, w's slot would be free.

Code: `eukhe-core/src/admission.rs` `ControllerState` (`has_room`,
`interactive_busy`, `hold`, `grant_waiters`, `preempt_background`,
`release`), `AdmissionController::admit`, `set_limits`,
`QueuedPermit::poll` and its `Drop`, `ProviderPermit`'s `Drop`. The daemon
supervisor's registry (`eukhe-daemon/src/provider_admission.rs`) runs
the same controller for every worker. The wait queues are
`BTreeSet<u64>` by ticket: `admission_fifo` says the waiting order is
ticket order, so a waiter that leaves is removed in O(log n), and a
preempted uncollected grant goes back to its place without a sort.

Tie: the admission bridge (`admission::bridge`) runs 400 scenarios from a
fixed seed (about 43,000 ops: limits 0 to 3, unlimited included, queue
limits 0 to 3, admits of both classes, polls, drops of permits and of
waiters, new limits) on the Rust `AdmissionController` and on
`bend/bridge_admission.bend`. After each op both print the outcome, the
snapshot, both queues, the background slots held, the uncollected
grants and the preempted permits; the test compares them byte for byte.
Breaks made on purpose and removed: the grant loop taking the newest
interactive waiter (`pop_last`), and a preempted uncollected grant not
put back in the queue: the bridge fails on both. The bridge found no
difference between the Rust code and the model. Not modelled: the
wakers (the bridge polls with a no-op waker; a grant takes the waker it
fires) and the daemon's connection frames.

### H4. Every run ends

A run is one user turn: model calls, tool rounds, retries, until it ends.

1. A run ends in one of: answered, aborted, failed. No other end exists.
2. A run makes at most `maxToolRounds` tool rounds (default 250; `0` takes
   the default). At the cap it ends as failed (`run_limit`), with a
   message that names the cap. A goal or autonomous continuation starts
   a new count: its own caps bound continuations.
3. A run that makes the same tool calls (name and arguments) with the
   same results `LOOP_ROUNDS` (6) rounds in a row ends as failed
   (`run_limit`, a loop). A call whose result changes (a job that makes
   progress) is not a loop.
4. A provider that answers "deferred" is polled at most `MAX_POLLS`
   (17,280: a day at the default 5 s) times; then the run fails
   (`model_error`).
5. Retries are bounded by `retry.maxRetries` (already true).
6. An abort ends the run within one phase: the phase driver races every
   phase handler, so every `before_request` hook and every wait in it,
   against the invocation's cancel signal. A handler that honours the
   signal returns at once; one that does not is dropped after
   `ABORT_GRACE` (3 s).

Changed from the first draft: the round count and the loop guard travel
in each generation's input (durable, so a restart keeps them), not in a
separate live-run field; a continuation resets them (item 2).

A deliberate difference from TS pi-durable: TS's `pi.generation` input
is always `{}`; eukhe's carries `{"rounds": {"count", "same", "hash"}}`
from the second generation of a run on. The cross-implementation
fixtures (`eukhe-durable/tests/fixtures/harness_cross/*-resumed*`) were
edited to that one field after TS wrote them; nothing else in them
changed.

Model: `bend/run.bend`. Its live phases are prepare, call (a request or
a poll), compact (an overflow's or a blocking threshold compaction) and
tools; its limits count down (rounds, compactions, retries, polls left).
Each step is one Rust decision: prepare `before_request`, a compaction's
end `after_compaction` (an overflow's needs its entry; a threshold one
fails the run only when it failed, not when it found nothing), a reply
`after_reply`, a round's end `Rounds::finish` then `RoundEnd::reset` (a
control stops the run uncounted; a queued reset ends it only after the
round counted, so the cap and the loop guard come first). Proofs:
`bend/proof_run.bend`. The measure `M` orders a run lexicographically
(rounds left, then compactions, retries and polls left in the
generation, then the phase) and writes that order as one mixed-radix
number: every input to a live run lowers it by at least one, and at the
start it is `bound(cfg)`. Every law is universal (any limits, any
inputs).

| Law | Says |
| --- | --- |
| `run_ends` | After `bound(cfg) = max(cap, 1)·(2 + (retries + 2)·(polls + 2))` inputs, whatever follows, the run has ended (H4.1, H4.4, H4.5). |
| `run_end_stays` | An ended run never changes (H4.1). |
| `run_abort_ends_now` | An abort ends a live run as aborted at the next step (H4.6). |
| `run_rounds_capped` | A run that has made `max(cap, 1)` rounds has failed (H4.2). |
| `run_rounds_fail_at_cap` | The round cap fails a run only once it has made exactly `max(cap, 1)` rounds (H4.2). |
| `run_loop_needs_repeats` | A loop fails a run only when its last `loop` rounds had the same calls and results (H4.3). |
| `run_polls_need_defers` | The poll cap fails a run only after `polls + 1` deferred replies in a row: the request's and each of its `polls` polls' (H4.4). |

Each of these breaks fails a proof: no poll cap, no round cap, a cap
that fails a run early, a poll count that a non-deferred reply does not
reset, a loop count that ignores the hash, an ignored abort in the tools
phase, a retry that does not spend a retry.

Code: `eukhe-durable/src/harness/generation/decide.rs` (`before_request`,
`after_compaction`, `after_reply`, `Rounds::finish`, `RoundEnd::reset`,
`MAX_POLLS`, `LOOP_ROUNDS`); `generation.rs` `prepare` (both decisions,
`compaction_end`, `threshold_compaction`), `classify` (the reply, then
the step), `GenerationInput.rounds`, `GenerationCheckpoint::Poll.polls`,
`request` (a failed hook fails the run), `abort` (every checkpoint ends
aborted); `generation/round.rs` `finish_tool_round`, `round_hash`
(SHA-256 of the calls and results, 53 bits); `scheduler/execution.rs`
`Inner::run` (the race, `ABORT_GRACE`); `harness/agent.rs`
`DEFAULT_MAX_TOOL_ROUNDS`; `eukhe-core/src/settings` `maxToolRounds`.

Tie: the bridge test `harness::generation::bridge::the_rust_decisions_equal_the_bend_model`
calls, at each phase, the production decision that phase calls
(`before_request`, `after_compaction`, `after_reply`, `Rounds::finish`,
`RoundEnd::reset`), keeps the counters the checkpoints carry, and runs
`bend/bridge_run.bend` on 401 generated scenarios (the production limits
and random small ones; every reply, threshold, compaction result, round
hash and end, and abort), comparing the phase and the counts left after
each input, byte for byte. Not in the bridge: the abort itself (the
`abort` handler has one outcome; H4.6's race is `Inner::run`), and the
run's other failures (no model, a failed request hook), which only end
it. Regression tests (`harness::generation::tests`):
`run_bounds::a_run_that_keeps_calling_tools_fails_at_the_round_cap`,
`the_same_calls_with_the_same_results_end_the_run_as_a_loop`,
`the_same_calls_whose_results_change_are_no_loop`,
`an_abort_ends_a_run_stuck_in_a_request_hook`,
`recovery::keeps_the_rounds_a_run_made_across_reopen`,
`fails_a_response_still_deferred_after_its_last_poll`.

### H5. Every subagent reports back exactly once

1. Every spawned child ends with exactly one end: a report to its parent
   (completed, failed, cancelled, stalled, unreachable), or none when the
   child already replied by an agent message or the parent itself
   cancelled it (the cancel's result is its answer).
2. A child that makes no progress for `subagentStallMs` (default 600 000;
   `0` or unset takes the default) is stopped (its run is aborted) and
   reported as stalled. Progress is the child's token: its session's event
   sequence plus the tokens of its own unsettled children plus the output
   its kernel's jobs wrote (the stdout/stderr bytes of its cells and the
   output bytes of its running `bash()` handles), so a child that
   streams, runs tools, waits on a busy child of its own, or waits on a
   background job that writes output (a long build) is never stalled. A
   job that writes nothing for `subagentStallMs` ends as a stall: jobs
   have no time bound of their own.
3. `CHILD_POLL_FAILURES` (5) failed polls in a row, while the child's
   worker lives or restarts, report the child as unreachable. Each failed
   poll doubles the pause before the next (2 s, 4 s, ... 32 s), so they
   span a minute. The pause is the polling session's own: a reopened
   parent polls at once, since only a poll tells it that the child's run
   was interrupted while it was down (fixed: a restarted parent waited
   out the pause its closed session scheduled, 4 s after a poll the
   daemon's own shutdown failed, and its roster read the interrupted
   child as `running` meanwhile). A worker that is gone settles the child
   at once (`worker-exited`). A stalled or unreachable child's run is
   aborted and then its agent is stopped through the `rlm` kill path (a
   plain kill: its worker is released, its session stays and a later
   prompt wakes it).
4. A report is delivered once: a resend has the same request id, and the
   parent drops a request id it knows. One rule delivers it: submit, wait
   until the submission settles, end once it is placed, and submit again
   under the next id only once it is withdrawn (a parent abort or close,
   or a withdrawal of that input). So at most one submission of a report
   is ever live (queued or placed), and a withdrawal that loses the race
   to a placement leaves the report placed. Resubmissions are at most one
   per withdrawal. A closing parent admits nothing: the report stays owed
   and the reopened session delivers it. An abort of the task that owes a
   report submits nothing: it hands the report (same ids, its withdrawals
   so far) to a new task in the report phase, which the abort does not
   reach, so every withdrawal, also one that races the abort, gets the
   next id (fixed: an abort that raced a withdrawal, or a second
   withdrawal after an abort, lost the report).

Changed from the first draft: 1 names `unreachable` and the two
report-less ends; 3 adds the backoff, the stop, and keeps the `Gone`
verdict; 4 names the one report rule and the hand-off.

Model: `bend/child.bend`. The watch's clock `W` counts down the ms of no
progress left (`left`) and the failed polls left (`tries`); `look` is the
verdict on one poll. The task (`St`, `step`) runs against an adversary:
polls with any reading and any delay, the parent's deliveries and
withdrawals of any submission id, its aborts, closes and reopens, and
task aborts and deletes, in any order. The parent's inbox keeps every
submission of the report with its fate (queued, withdrawn, placed); the
task reads its submission's fate by id. Proofs: `bend/proof_child.bend`.
Every law is universal.

| Law | Says |
| --- | --- |
| `child_stalls_in_time` | Quiet polls (same token, or failed), at least as many as the ms left, end the watch (H5.2). |
| `child_unreachable_in_time` | Failed polls in a row, as many as the tries left, end the watch (H5.3). |
| `child_clock_bounded` | The clock never grows past full, so the two bounds are at most `subagentStallMs` ms and `CHILD_POLL_FAILURES` polls (H5.2, H5.3). |
| `child_progress_is_not_a_stall` | A poll with a new token continues the watch with a full clock (H5.2). |
| `child_one_live` | After any events, at most one submission of the report is live (queued or placed) (H5.4). |
| `child_report_once` | After any events, at most one submission of the report is placed: the transcript holds it at most once (H5.4). |
| `child_resubmits_per_abort` | The report's submissions are at most 1 + the parent's aborts, closes and withdrawals (H5.4). |
| `child_delivered_once` | After any events, a report the task owes is placed exactly once when the parent reopens, the task takes three steps and the parent's run places the id the task then waits on (H5.4). |

Rust (paths from `crates/`):

- `eukhe-core/src/durable/children/watch.rs`: `Vigil::judge`, the pure
  verdict (`look`); `CHILD_POLL_FAILURES`.
- `eukhe-core/src/durable/children/task.rs`: the `watch` phase keeps the
  `Vigil` in its checkpoint, skips the pause on its first poll in a
  session (`ChildrenServices.polled`), aborts then stops a stuck child
  (`host.cancel`, `host.stop`) and reports it
  `Failed{stalled|unreachable}`; `watched_next` is its next state; the
  `report` phase follows `report_step`, the one report rule (`owe`), on
  its submission's `Fate`; `abort` hands the report `owed_on_abort` picks
  (`cut.ph`) to a new task (`ChildTaskInput.owed`, the row's `reporter`,
  which the quiescence barrier waits on).
- `eukhe-daemon/src/worker/run_outcome.rs`: the progress token in the
  `get_run_outcome` reply (`RlmChildOutcome`), with the kernel's job
  output (`ReplKernelManager::job_output_progress`).
- `eukhe-daemon/src/rlm_children/durable_host.rs` `wait_settled`: a failed
  probe of a live or restarting worker is a failed poll (it answered
  `Running` before, forever); `stop` is the plain kill.
- `eukhe-core/src/settings`: `subagentStallMs`.

Tie: the bridge tests
`durable::children::watch::bridge::the_rust_watch_equals_the_bend_model`
(40 scenarios of 300 polls each, `bend/bridge_child.bend`) and
`durable::children::task::bridge::the_rust_report_rule_equals_the_bend_model`
(300 scenarios of 80 events: task steps, deliveries and withdrawals of
any id, aborts, closes, reopens, cancels and deletes, against `step`
through `bend/bridge_report.bend`; it drives `watched_next`,
`report_step` and `owed_on_abort` over an inbox kept as the harness
keeps it). Regression
tests: `durable::children::tests::watch::a_hung_child_is_stopped_and_reported_stalled`,
`failing_polls_report_the_child_unreachable`,
`a_progressing_child_outlives_the_stall_budget` (a guard: progress is
never a stall), `tests::report_delivery::a_report_withdrawn_as_its_task_aborts_is_delivered_once`
(three stops in a row, each withdrawing the report), daemon
`rlm_children::durable_host::tests::a_live_child_whose_probes_fail_is_a_failed_poll`,
`stopping_a_child_kills_its_worker_once_and_keeps_its_session`, core
`kernel_lifecycle::background_bash_output_moves_the_job_progress` and
`kernel::manager::events::tests::stream_output_moves_the_job_progress`
(a child idle on a long job that writes output is not stalled).

### H6. Every other wait has an exit

Every wait races three things: the event it waits for, a deadline, and the
cancel signal. The first one wins; the wait ends exactly once.

1. A request to a chat memory owner in another process has a reply
   deadline (30 s; for a settled view, the settle deadline plus 30 s; for
   an import, 100 ms per item plus 30 s, since the owner fsyncs each
   item). A miss is an error that the turn shows. This process's own
   owner has none: its actor thread is the process's own work, and the run's
   cancel ends the wait (H4.6). A request transform (`before_request`
   hook) that fails fails the turn: the request never goes out with
   another prompt in silence.
2. The root-turn lease is first come, first served. A waiter that stops
   waiting never gets it, a crashed holder's lease is freed, and a free
   lease goes to the next live waiter at once. The wait itself has no
   deadline (it waits for another window's turn); it ends with that
   turn, or with the run's cancel (H4.6 drops the hook that waits), and a
   dropped wait leaves nothing behind.
3. The stream stall clock starts when the request has its admission slot,
   not before: a long queue is not a stall.

Changed from the first draft: item 4 (`bash.defaultTimeoutMs`) is
dropped. No eukhe session installs the durable `bash` tool
(`eukhe-durable/src/tools/bash.rs` has no product caller); the model runs
shell commands through the `ipython` kernel's `bash()`, whose cell
blocks the turn at most `toolBlockingBudgetMs` and then goes on as a
detached job (`durable/rlm/tool.rs`), and `jobs.wait` is clamped to the
same budget. Item 1 gained the failed transform, item 2 the lease's own
laws.

Models: the wait in `bend/wait.bend` (a wait sees, one at a time and in
any order, its event, ticks, and the cancel; its deadline is a number of
ticks or none); the lease in `bend/lease.bend` (asks, releases, stops and
crashes in any order; a key is the order of arrival). Proofs:
`bend/proof_wait.bend`, `bend/proof_lease.bend`. Every law is universal.

| Law | Says |
| --- | --- |
| `wait_ends_once` | A wait ends exactly once when its event, its cancel or its deadline comes, and never otherwise. |
| `wait_end_is_final` | Once the cancel or the deadline came, the wait has ended: what comes after changes nothing. |
| `wait_arrival_wins` | An event before the cancel and the deadline ends the wait with the event. |
| `wait_cancel_wins` | A cancel before the event and the deadline ends the wait as cancelled. |
| `lease_fifo` | After any events, the holder asked before every waiter, and the waiters wait in the order they asked (H6.2). |
| `lease_never_idle` | After any events, the lease is held or no live waiter waits: a release or a crash hands it on at once (H6.2). |
| `lease_keeps_waiters` | In any state, an event that does not end a live waiter (its release, its stop, its origin's crash) leaves it waiting or holding: no waiter is skipped (H6.2). |
| `lease_stop_never_holds` | A waiter that stopped waiting never holds the lease, whatever comes after (H6.2). |
| `lease_crash_frees` | In any state, a crash ends every lease of its origin, held or waited for (H6.2). |

Code: `eukhe-chord/src/context.rs` `race` (the one race of event,
deadline and cancel; `Exits`, `Raced`); `memory/service.rs`
`Request::reply_deadline`, `answered`, `Memory::request`, `live_parts`;
`memory/service/turn.rs` `Turns` (the lease), `Memory::acquire_turn`
(the turn file is polled, `TURN_FILE_POLL`), `TurnLease::release`;
`eukhe-durable/src/tasks/runtime.rs` `HookRunner::each_required`, which
`harness/generation.rs` `request` runs the `before_request` hooks with
(a failure ends the run as `model_error`); `eukhe-ai/src/utils/stream_idle.rs`
`StreamClock`, `ClockHold` (`ProviderRequestOptions::stream_clock`);
`durable/admission_gate.rs` `AdmissionGate::admitted` (holds the clock
while the request waits for its slot).

Tie: the bridge `memory::service::turn::bridge` runs `race` on paused
tokio time (a oneshot event, ticks of `advance`, an `AbortController`)
and `Turns` (asks, releases, dropped replies, closed connections)
against `bend/bridge_wait.bend` on 304 wait and 200 lease scenarios,
byte for byte. The `wait_*` laws are about `race`, not about each wait:
the deadline each wait passes to it is tied by tests.
`memory::service::waits::every_request_to_a_remote_owner_but_the_lease_has_a_reply_deadline`
checks `Request::reply_deadline` for every request (its match has no
catch-all, so a new request takes a side). Regression tests:
`memory::service::waits::a_stuck_owner_fails_the_request_at_its_reply_deadline`,
`a_dropped_wait_for_the_turn_file_leaves_nothing_behind`;
`durable::admission_gate::tests::a_queue_longer_than_the_idle_deadline_is_not_a_stall`
(fails as stalled without the clock hold);
`durable::optchat::tests::a_failed_transform_fails_the_turn_and_sends_nothing`.
Not modelled: how long the owner's own work takes (the reply deadline
bounds the wait, not the work), and the turn file between owners.

### S1. The session tree

One tree holds the state of a session. Each node has an id, a parent and a
value. The id of a node is more than the id of its parent. The root (id
`0`) is the parent of the top nodes. The root is not a node.

1. A record changes the tree. A `Do` record holds one checked change: a
   `Put` sets a node, and a `Del` removes a node and every node below it.
   The tree rejects a `Put` whose parent is not the root or a node, and a
   `Del` of the root. A rejected record does not change the tree.
2. A `Rewind` record holds exact changes back to an earlier tree. The tree
   rejects a rewind whose result is not a sound tree.
3. The journal keeps every record in order. A replay of the journal makes
   the live tree. A replay of a prefix is a snapshot. The cursor is the
   number of records.
4. A rewind plan compares the live tree with a snapshot. It stops each
   node that goes, starts each node that comes back, and restores each
   node that changes.

The state tree of a session is a session tree that the commits of its
storage make. The disk format does not change: the tree comes from the
same commits that `main.jsonl` holds.

1. Each stored record is a node: a conversation, an entry, a task, a
   submission, or a document. A conversation hangs under the
   conversation of the task that owns it, else under the conversation
   that it forks from, else under the root. An entry, a task, and a
   submission hang under their conversation. A session document hangs
   under the root. A conversation document hangs under its conversation.
   A task document hangs under the conversation of its task.
2. So the parent of each node is the root or a conversation, and no
   commit deletes a conversation. The stored history does not keep the
   early states of a terminal task, but each node still finds its
   parent. A build from the history first learns the conversation of
   each task.
3. Each change of a commit is one `Do` record. A new or changed record is
   a `Put`. A retired document is a `Del`. A copied document is a `Put`.
   The changes of a commit come in no order: a `Put` waits until its
   parent is in the tree.
4. A change whose parent or node is not in the tree is a typed error
   (`StateError`). The tree does not change, and the session logs the
   error. Nothing is dropped in silence.
5. The value of a conversation, a task, and a submission node is its
   record as JSON. An entry node keeps its kind, conversation, head, and
   task. A document node keeps its kind, key, scope, the commit that
   made it, and the commit that last changed it.
6. Ids go to records in the order that the tree first sees them. A
   commit at or before the last commit of the tree counts once.
7. On open, the storage keeps its replayed history. A background task
   builds the tree from it. Then the task records each commit of the
   Harness. The commit listener only puts the commit in a queue, so no
   commit waits for the tree. Open and attach do not wait for the build.
   A read waits until the build ends. If the build or a record panics,
   the tree stops: it ends its commit subscription, and a read gets an
   error.
8. The ids and the cursor hold for one worker. A tree built again from
   the stored history can see the records in another order. After a
   worker restart, a client reads a new snapshot.

The wire has a one-shot read and an opt-in subscription.

1. `get_state_tree` gives the snapshot (with its cursor), or the records
   after the cursor `since`. `get_state_rewind_plan` gives the effects of
   a rewind to a cursor.
2. `subscribe_state_tree` gives the same reply. The supervisor adds the
   connection to the session's state tree subscribers before the worker
   reads the tree. Then the connection gets a `state_tree_update` frame
   (`from`, `cursor`, and the records) after each commit that adds
   records. So the frames cover every record after the reply's cursor.
3. A frame can repeat records that the reply had. A client skips a frame
   whose `cursor` is not more than its own cursor. For the other frames,
   it applies the records from its own cursor. A frame whose `from` is
   more than the client's cursor shows a loss: the client subscribes
   again.
4. `unsubscribe_state_tree` or a closed connection ends the subscription.
   A connection that does not subscribe never gets the frame. The frame is
   not a session event: it takes no event sequence, so the replay cursors
   of other clients do not change. A direct session client of the worker
   never gets the frame.

Model: `bend/tree.bend`. Laws: `LAWS.bend` section (S1). Proofs:
`bend/proof_tree.bend`. Every law is universal: every record is free (any
put, valid or not, any delete, any rewind ops).

| Law | Says |
| --- | --- |
| `tree_apply_sound` | A record keeps a sound tree sound: the ids are in order, and every node hangs under the root or a node (no orphan, no cycle) (S1.1, S1.2). |
| `tree_replay_sound` | Every journal makes a sound tree (S1.3). |
| `tree_snapshot` | A snapshot after a prefix of the journal, with the records after it, makes the tree of the whole journal. A client that holds a snapshot and gets the records after it holds the live tree (S1.3). |
| `tree_rewind_reaches` | A rewind with the diff from the live tree to a target makes the target exactly (S1.2, S1.4). |
| `tree_rewind_still` | A rewind to the live tree has no changes (S1.4). |
| `tree_rewind_minimal` | Each change of a rewind is on a node that differs between the live tree and the target: a rewind starts, stops, or restores only what changed (S1.4). |
| `tree_delete_removes` | A delete removes its node (S1.1). |
| `tree_delete_only_below` | A delete removes a node only when it is the deleted node or its parent goes: it removes the subtree, nothing else (S1.1). |
| `tree_delete_within` | A delete changes no node that it keeps (S1.1). |
| `tree_put_sets` | A put under the root or a node sets its node (S1.1). |
| `tree_put_keeps_others` | A put changes no other node (S1.1). |

Code: `eukhe-durable/src/tree/mod.rs` `SessionTree::apply`, `TreeRecord`,
`TreeOp`; `tree/journal.rs` `Journal` (`push`, `replay`, `snapshot_at`);
`tree/diff.rs` `diff`, `rewind_to`, `rewind_effects`; `tree/state.rs`
`StateTree` (`record`, `from_history`, `record_writes`, `records_since`, `snapshot_at`,
`rewind_plan`); `storage/jsonl/storage.rs` `CommitHistory`,
`JsonlStorage::take_history`; `eukhe-core/src/durable/state_tree.rs`
`LiveStateTree`; `eukhe-daemon/src/worker/state_tree.rs` (the
`get_state_tree`, `subscribe_state_tree`, and `get_state_rewind_plan`
requests, and the `state_tree_update` frame);
`supervisor/clients.rs` (the subscription, `state_tree_subscribers`);
`supervisor/supervision.rs` (the frame routing); `peer.rs`
`ConnectionRole::streams`; `eukhe-cli/src/daemon_command.rs` `run_state`
(`eukhe state`, `eukhe state --follow`, `eukhe state rewind-plan`).

Tie: the bridge test `tree::bridge::the_rust_tree_equals_the_bend_model`
runs `Journal` and `bend/bridge_tree.bend` on 300 generated scenarios
(checked puts and deletes, saves, rewinds to a save, raw rewinds, and
replays of the journal) and compares the transcripts byte for byte. The
scenarios reach every rule of the model. Regression tests:
`tree::state::tests::commits_build_the_tree_with_parents_first`,
`storage_writes_build_the_same_journal_as_publications`,
`a_rewind_plan_stops_starts_and_restores`,
`a_history_gives_every_node_its_conversation`,
`an_unknown_parent_or_node_is_an_error`;
`jsonl_storage::keeps_the_replayed_and_later_commits_until_the_history_is_taken`;
`durable::open::tests::the_state_tree_follows_the_history_and_the_live_commits`;
the daemon tests `get_state_tree_answers_the_sessions_tree` and
`subscribe_state_tree_streams_records_to_its_connection_only`;
`peer::tests::peer_session_attach_gates_event_stream`. Not modelled:
the map from commits to records (S1, second list). Its tests tie it.

### S2. Jobs and limits

One setting bounds every output: the output of a tool call, of a cell,
and of a job. A tool call journals only its start and its settle.

Limits:

1. The setting is `Truncation`. `On(OutputLimits)` keeps at most the
   limits (bytes, lines, head or tail) and counts the rest as dropped. It
   is the default, with 50 KiB and 2000 lines. These default values are
   in `eukhe-types` only. `Off` is the explicit opt-out: it keeps every
   byte.
2. The bytes kept and the bytes counted as dropped are every byte the
   output produced. No byte is lost in silence. A cap drops nothing from
   output that fits.
3. A tool sets its value in `ToolRegistration.truncation`. The harness
   resolves the value of a call in one place (`reporting_for`). A tool
   reads the value through `ToolExecutionApi::truncation`. Under `Off` the
   final result is not truncated.
4. `BoundedOutput` (eukhe-core) takes its bound from the same value. Past
   the bound it writes the full output to an artifact file. Under `Off` it
   keeps everything and writes no artifact.

A tool call:

1. A call journals two records: its start (the slot becomes `running`,
   with its `execute` checkpoint) and its settle (the slot becomes `done`,
   in the same commit as the result entry). No progress update is
   journaled: no output, no details, no diagnostics, no usage.
2. While the call runs, each progress update goes to the in-memory
   progress board of the Harness. The board sends each change to the live
   observers of the conversation. `watch_events` gives, in its first
   snapshot, the last progress of each running call. Then it gives each
   change as one `tool_execution_update`. No update comes after the end of
   the call.
3. The settle carries everything the call reported: every result byte,
   every warning, and all usage. A call records usage while it runs with
   `ToolExecutionApi::usage`. An abort settles from the board, so it
   carries the output that the call reported, published or not. The board
   keeps the call until its settle commits, so a settle that did not
   commit, and the abort settle after it, read the same progress.
4. Crash behavior changed. Before S2, each progress update was a commit
   to `pi.live`, so a call that a crash interrupted settled with the
   output it had committed. Now the board is lost in a crash. The partial
   live output, details, diagnostics and usage of the interrupted call are
   lost; the call settles from what is durable. When the call wrote a
   `BoundedOutput` artifact, the artifact keeps the full output.
5. A structural view (`view_state`) holds committed state only. So it
   shows the slot of a running call without its output. Use
   `watch_events` for live output.

Jobs (from the jobs slice):

A job is work that runs long: a user bash, or an `ipython` cell whose call
outlived the blocking budget. Each job has an output, one end, and a kill.

1. A job counts its output under the output cap of the session
   (`Truncation`; on by default). Under a cap of `c` bytes it keeps at most
   `c` bytes and counts the rest as dropped. The opt-out (`Truncation::Off`)
   keeps every byte. The bytes kept and the bytes dropped are every byte
   the job wrote. A cell or a script becomes a job when its call detaches;
   the job starts with the bytes the run wrote before (`JobSpec::written`),
   so it also counts every byte of the run.
2. A job ends once: it exits with a code, or the kill signal ends it. The
   end goes to the session's job writer. The job ignores every event after
   its end.
3. A kill sends the kill signal through the owner of the job: a user bash
   kills its process group, also when the command closed its stdout and
   stderr; a cell is interrupted and its kernel is killed after the
   grace. The owner reports the end that follows, so a job can end some
   time after its kill.
4. A blocking call on a job waits at most until its deadline, within the
   blocking budget of the session (`toolBlockingBudgetMs`). It answers
   `Settled` with the end when the job ends first. Else it answers
   `Detached` at the deadline, and the job goes on in the background. A
   deadline that has passed detaches at once, even when the end is ready.
   One function (`jobs::wait_until`) does every blocking wait on a job:
   the `ipython` call and its wait on a cell that holds the kernel,
   `jobs.wait`, `jobs.cancel`, and `execute_bash_and_wait`. Past the
   budget, `execute_bash_and_wait` answers `detached: {job, budgetMs}` with
   the output so far; the end of the run records its `eukhe.bash` row.
5. The start and the end of a job are session state; its output is not.
   The start creates the session document `eukhe.job` (key: the job id);
   the end retires it. So the state tree (S1) holds one node, under the
   root, for each running job. A writer task commits the records in order,
   a batch per commit, and no caller waits for it. A job that starts and
   ends in one batch commits nothing. When a batch fails, the writer
   commits its records one at a time; an end whose node is absent retires
   nothing. A record that fails alone goes to the main conversation as a
   `job_record_failed` notice. On open, the writer retires the job nodes
   that the history left (their jobs ended with the old process).
6. A rewind stops the orphan jobs. When `navigate_tree` or `fork` takes
   the session back to an earlier entry (none: before every entry), the
   session kills every running job that started after that entry was
   committed, and keeps every other job as it is. These are the jobs
   whose nodes the state tree just after that entry does not hold. The
   order comes from the entry commits that the job table sees when the
   commits occur (`JobTable::rewind_to`), not from the job nodes: the
   writer commits a node later, so an entry can come before the node of a
   job that started before it. An entry from before the open comes before
   every job. The session then waits for the ends of the killed jobs, at
   most the blocking budget. The response names the jobs that ended in
   that time (`stoppedJobs`) and the jobs that had not ended yet
   (`stoppingJobs`).
7. While a job runs, the system prompt has the section `running-jobs`. It
   gives the number and the ids of the job nodes of the state tree. The
   section is absent while no job runs.

Model: `bend/job.bend` (`step`, `ends`, `wait`, `journal`, `rewind`).
Laws: `LAWS.bend` section (S2). Proofs: `bend/proof_job.bend`. Every law
is universal: every event is free (any output size, exit, kill or tick,
in any order; any cap or the opt-out; any budget; any tool call stream;
any job table).

| Law | Says |
| --- | --- |
| `job_output_bounded` | With a cap, a job keeps at most the cap of its output (limits 1, jobs 1). |
| `job_no_silent_loss` | The bytes kept plus the bytes dropped are every byte the job wrote before its end (limits 2). |
| `job_optout_keeps_all` | With the opt-out, a job drops nothing (limits 1). |
| `job_cap_drops_only_excess` | A cap drops nothing from output that fits (limits 2). |
| `job_ends_once` | A job reports exactly one end once it exits or is killed, and none before (jobs 2). |
| `job_end_is_final` | An ended job stays as it ended: no late output, no second end (jobs 2). |
| `job_kill_ends_now` | A kill ends a live job at once, as killed, with its output kept (jobs 3). |
| `call_blocks_at_most_budget` | A blocking call returns once its budget has passed (jobs 4). |
| `call_settles_with_job` | A call that settles in time reports the job's own end, and the job has no other end (jobs 4). |
| `stream_journals_two` | A tool call journals at most two records; no progress update is journaled (call 1). |
| `stream_settles_once` | A tool call settles exactly once when it ends (result or cancel), and not before (call 1). |
| `stream_settle_carries_all` | The settle carries every result byte, every warning, and all usage (call 3). |
| `rewind_stops_orphans` | After a rewind, every running job is a job of the target tree (jobs 6). |
| `rewind_keeps_target_jobs` | A rewind leaves every job of the target tree as it was (jobs 6). |

Gap: in the model, `rewind` stops a job at once (`stop.at` sets `running`
to false), and the bridge kill records the end at once. So the two rewind
laws are about the kill decision: which jobs get the kill and which do
not. The real kill only sends a signal (the user-bash cancel, the shell
task abort, the cell interrupt), and the job ends later, or not when its
process ignores the signal. The code does not claim more than the model:
a rewind names a job in `stoppedJobs` only when its end came within the
wait, else in `stoppingJobs`.

Code: `eukhe-durable/src/harness/output.rs` (`Truncation`,
`OutputLimits`, `OutputBuffer`); `harness/tool/invocation.rs`
(`reporting_for`, `publish_progress`, `final_result`, the
`ToolExecutionApi` methods `truncation` and `usage`); `harness/tool.rs`
`settle` (takes the call's progress from the board); `harness/live/progress.rs`
(the progress board); `harness/events.rs` `watch_events`;
`eukhe-types/src/output.rs` (the default limits);
`eukhe-core/src/durable/bounded_output.rs` (`BoundedOutput::in_session`);
`eukhe-core/src/durable/jobs/mod.rs` (`Job`, `JobState::step`, `JobTable`
(`start`, `rewind`, `rewind_to`, `observe`), `wait_until`); `jobs/tree.rs` (the `eukhe.job`
document, the writer, `stop_orphans`, `running_jobs_section`);
`durable/rlm/jobs.rs` (`CellJobs`: the cell board over `Job`;
`jobs.list`, `jobs.wait`, `jobs.cancel`); `durable/rlm/tool.rs` (the
`ipython` call's wait and detach); `durable/prompt.rs` (the
`running-jobs` section); `eukhe-daemon/src/user_bash.rs` (`UserBash`:
every run is a job; `execute_bash_and_wait` detaches at the budget);
`branch_navigation.rs` (`navigate_tree` and `fork` stop the orphans).

Ties: three bridge tests compare transcripts with a Bend file byte for
byte.

- `harness::output::bridge::the_rust_output_bounder_equals_the_bend_model`
  runs `OutputBuffer` and `bend/bridge_stream.bend` on 300 generated
  scenarios: a cap (head or tail retention) or the opt-out, chunks of
  output, and the end of the output, with chunks after the end.
- `harness::tool::tests::bridge::a_real_tool_calls_journal_equals_the_bend_model`
  runs 40 real tool calls on a Harness (result bytes, warnings, usage,
  then a return or a cancel). It records every `pi.live` commit from the
  start of the call and prints `start`, `settle` (read from the result
  entry), or `progress` for any other commit in the call's slot. The
  model has no `progress` record, so a journaled progress update fails
  the test.
- `durable::jobs::bridge::the_rust_jobs_equal_the_bend_model` runs `Job`,
  `wait_until` (on the paused tokio clock; a tick is one millisecond) and
  `JobTable::rewind` with `bend/bridge_job.bend` on 300 generated
  scenarios. The scenarios reach every case: truncation, opt-out, kill,
  quit, an event after the end, a detach at the budget, a settle within
  it, a rewind that stops a job and one that keeps a job.

Regression tests:
`harness::generation::tests::live_deltas::a_long_streaming_call_commits_nothing_between_its_start_and_its_settle`
and the other `live_deltas` tests (what each publication delivers, and no
commit); `settles_an_aborted_tools_slot_with_its_status_and_entry_only`;
the eukhe-core `bounded_output` tests (the limits of a call and the
opt-out); `durable::jobs::tests` (the cap and one end, the opt-out, the
rewind kill, the wait);
`durable::open::tests::jobs_are_state_tree_nodes_the_prompt_shows_and_a_rewind_stops_the_orphans`;
the daemon tests
`user_bash::tests::an_awaited_run_past_the_budget_answers_detached_and_its_end_records_its_row`
and `branch_navigation::tests::navigate_tree_stops_the_jobs_started_after_its_target`.
Not modelled: the map from jobs to documents and from entries to tree
cursors (jobs 5 and 6), and the board's delivery order; the tests above
tie them.

### S3. The host and the sandbox

The host decides; the sandbox executes. The sandbox is the kernel (the
Python stub of a session): it sends frames to the host, one JSON object
per line. A subagent can work in a sandbox of the workspace too: a copy
of its parent's files.

The protocol:

1. The host reads the frames of the kernel in order. One gate decides on
   each frame, before any handler sees it.
2. A host request within the size limit, of a type the host serves, and
   with an id it did not see before, is accepted. Only an accepted frame
   reaches a handler, and every accepted frame reaches one. The handler's
   result or error is its one reply.
3. A host request over the size limit gets one error reply and does
   nothing. The host reads only the head of the frame (the runtime
   writes `event` and `id` first) and drops the rest, up to its newline.
   The session keeps working.
4. A host request of a type the host does not serve, without a type, or
   with a used id gets one error reply and does nothing. The reply to a
   used id has the status `duplicate`, not `error`. It goes out under the
   id of a request that can still be in flight, so the runtime drops it
   (`_resolve_host_reply`) and the host writes a diagnostic. Only the
   handler's reply settles the first request with that id.
5. Other events answer the host's own requests and need no reply. An
   oversized stream or display event is dropped with a diagnostic.
6. A frame the host cannot answer is a typed fault (`ProtocolFault`): a
   line that is not UTF-8, a line that is not a protocol frame, or an
   oversized line with no host-request header. The protocol repair then
   replaces the kernel. It is loud: the request in flight fails with the
   fault.
7. The limits are constants in one place (`frames.rs`): the line limit
   (32 MiB), the head the gate reads (4 KiB), and the ids it keeps
   (1024). The runtime fails a cell whose `display` or `host_request`
   payload is over 16 MiB before it writes the frame.

The gate decides on the frames in order, and the refusals are written in
that order. The reply of an accepted request comes when its handler
ends, and the kernel matches it by id: a long request (`rlm.run`) does
not hold back a short one.

A subagent's workspace:

1. `rlm.spawn(..., workspace="isolated")` gives the child its own copy of
   the parent's workspace. `workspace="shared"` (the default) keeps
   today's behavior: the child works in the parent's directory.
2. At the spawn, the host copies the tracked and the untracked, not
   ignored files of the parent's directory (`git ls-files`; without git,
   the files its `.gitignore` files do not ignore) two times: the base
   (the workspace as the child found it) and the child's copy (its
   working directory). It never copies `.git`, `target/`, or another
   ignored directory. A directory of more than 100,000 files is refused
   (`MAX_WORKSPACE_FILES`): the spawn fails and names `shared`. The
   hand-back lists the child's copy with its `.gitignore` files only.
   `.git/info/exclude` and the global excludes do not apply there, so a
   file of the child that only they ignore comes back to the parent.
3. A copy clones the file's extents where the filesystem can (FICLONE on
   Linux: btrfs, XFS; clonefile on macOS: APFS). Elsewhere it copies the
   bytes and logs a warning with the counts. It never copies in silence.
4. At the child's end (its run answers, fails, or stalls, or the parent
   cancels or deletes it), the host first stops the child: its worker,
   its kernel and its background jobs end, and its session stays. Then
   the host takes the child's changes back into the parent's directory,
   path by path:
   - a path the child did not change keeps the parent's content;
   - a path only the child changed gets the child's content (a removal
     too);
   - a path both changed to the same content keeps it;
   - a path both changed to different contents keeps the parent's
     content and is a conflict. The child's version stays in the
     workspace's `conflicts/` directory.
   - a path the child changed that the parent cannot hold as a file (a
     directory is at that path, or a file or a symlink is where one of
     its directories goes) keeps the parent's entry and is a conflict.
     The child's version goes to `conflicts/`, and the hand-back
     continues with the next path.
5. The child's report and its roster row (`rlm.collect`,
   `rlm.list_subagents`) carry the hand-back: the paths taken, the
   conflicts, and where the child's versions are. A hand-back that fails
   is reported too, and the copy stays.
6. Each path is replaced in one rename, from a copy beside it. The copy
   has the same name in every run, so a run after a crash removes the
   copy that the crash left. The hand-back is idempotent: a path already
   taken reads as changed by both to the same content. So a hand-back
   that a crash cut runs again from the start to the same result. Its
   record (`handback.json`) ends it, and a repeat after the record does
   not stop the child again. Then the base and the copy are removed, and
   the child's directory becomes a symlink to the parent's, so a child
   woken later starts its kernel there.
7. The workspace lives in `<agent dir>/workspaces/<parent session id>/<child id>/`.
   A child that resumes after a daemon restart keeps its copy and its
   base: its stored working directory is the copy.

Why the default is `shared`: the prompts tell the parent to fan in
through files the children write while they run ("Have children write
files and read those files for fan-in", `prompts/layers/usage.md`), and
a child replies with `agent_message` before its run ends. An isolated
child's files reach the parent only at the end. Isolation is for
children that change the same tree in parallel.

Where the sandbox runs (the kernel transport):

1. The setting `kernelTransport` selects the transport of a session. When
   it is not set, the transport is `Local`: the kernel is a child process
   of the host, in its own process group, with the host's environment.
   This is the behavior before the transport.
2. When it is set, the transport is `Wrapped`. The kernel command runs
   under the wrapper's argv (`argvPrefix`). The same stub then runs in a
   container (`docker exec -i <c>`, `podman exec -i <c>`,
   `docker run -i --rm -v ...`), in a VM, or on a remote machine
   (`ssh -T <host>`, with `"command": "shell"`). The NDJSON frames and
   the frame limits do not change: the wrapper carries stdin and stdout.
3. The wrapped kernel does not get the host's environment. It gets the
   kernel's own entries, the host variables that `env` names, and
   `EUKHE_KERNEL_OWNER=stdin`. An entry that holds a host path
   (`EUKHE_CODING_AGENT_DIR`, `EUKHE_BASH_SHELL`) gets its sandbox path,
   or it is left out with a diagnostic. The wrapper process itself keeps
   the host's environment (docker and ssh need it). The sandbox has its
   own interpreter with eukhe-runtime (`python`, default `python3`); the
   host's kernel venv is not built for it. A Python skill imports in the
   sandbox when a mount holds its directory: its sandbox path goes in
   front of `PYTHONPATH`. Its dependencies must be in the sandbox.
4. `pathMap` lists the shared mounts: each one is the same directory at
   `sandbox` and at `host`. The kernel starts in the sandbox path of the
   session's cwd. A cwd outside every mount stops the start with an error.
   The deepest mount that holds a path maps it.
5. An `fs.*` host request (`read`, `write`, `edit`, `grep`, `glob`) comes
   with the sandbox's paths. The host maps its cwd and each path argument
   (the paths of the `edit` section headers and `MV` rows too) to host
   paths before a handler sees it. It maps the paths of the reply
   (`absolute`, `destination`) back. A path outside every mount, or a
   path relative to the sandbox's home (`~`), gets the typed rejection
   (`FsError`, reason `outside`, version `transport@1`), and no handler
   runs. "Outside" is checked on the host's disk too: the host resolves
   the symlinks of the longest part of the host path (and of the cwd)
   that exists, and the result must be in the resolved host directory of
   a mount. So a symlink in a mount that points out of every mount, or a
   `..` after such a symlink, gets the same rejection.
6. The namespace snapshot of a wrapped kernel is written at the sandbox
   path of the snapshot file. When no mount holds that file, the host
   does not ask for a snapshot, and it writes a diagnostic.
7. The lifetime follows the transport. A local kernel watches the host's
   pid (`EUKHE_KERNEL_OWNER_PID`). A wrapped kernel watches its stdin:
   at start it makes a process group of its own, and at stdin EOF it
   shuts down. When a synchronous cell holds the loop, it exits after 30
   seconds from the reader's side.
8. A kill closes the kernel's stdin and then signals the wrapper's
   process group. The wrapper ends, and so the stub sees its stdin close.
   The host reaps the `bash()` process groups of a local kernel from its
   journal. It cannot reap a remote process group: the pids are not the
   host's. The stub's own shutdown and its stdin-EOF exit kill those
   groups.

An example (`settings.json`; a project scope that is not trusted cannot
set it):

```json
"kernelTransport": {
  "argvPrefix": ["docker", "exec", "-i", "box"],
  "python": "/opt/venv/bin/python",
  "pathMap": [{ "sandbox": "/work", "host": "/home/me/project" }],
  "env": ["LANG"]
}
```

`@remote`: a kernel function that the host offers as a tool.

1. `@remote` (`rlm.remote`) records a Python function and announces it
   with the host request `remote.register`: its name, its module and
   qualified name, its docstring, and the JSON schema of its keyword
   arguments (from the type hints). A parameter that cannot be given by
   keyword is refused.
2. The session adds it to the tool surface as `remote/<name>`. The model
   reaches it through `dyn` only (S7): it never enters the roster.
3. A call goes to the kernel of the calling conversation as the request
   `call` (`module`, `function`, `args`). It uses the dedicated lane, so
   it does not wait for a cell, and a cell does not wait for it. The
   `done` frame gives the result or a typed error (`RemoteCallError`):
   not running, unreachable, unknown, timeout, failed. A kernel that
   stops or restarts before it replies gives `unreachable` at once, not
   a timeout at the end of the bound. Wrong arguments give `failed` with
   the `TypeError` text. A result that strict JSON cannot carry (NaN,
   Infinity) gives `failed` (kernel reason `unencodable`); the frame
   stays valid JSON, and the kernel keeps working.
4. The session's blocking budget (S2, `toolBlockingBudgetMs`) bounds the
   call. The kernel runs a synchronous function on its own daemon
   thread. A function that hangs costs that thread: the call answers
   `timeout`, and the kernel serves the next cells and calls. The result
   of the `dyn` call keeps the S2 output limits.
5. An `async def` function runs on the kernel's event loop, not on a
   thread. If it blocks without `await`, the whole kernel stops until it
   returns: cells and other calls wait, and its timeout cannot fire. Do
   blocking work in a synchronous function.

Model: `bend/sandbox.bend` (`serve`, `merge1`, `back`). Laws: `LAWS.bend`
section (S3). Proofs: `bend/proof_sandbox.bend`. Every input is free:
any frames of any length and kind, any limits, any workspaces of the
parent, the base and the child.

| Law | Says |
| --- | --- |
| `proto_one_reply_each` | Every frame gets exactly one reply, in order (S3.1, S3.2-4). |
| `proto_runs_only_accepted` | The host runs only frames it accepts: within the size limit and of an allowed kind (S3.2). |
| `proto_runs_every_accepted` | The host runs every frame it accepts (S3.2). |
| `proto_rejects_oversize` | A frame over the size limit gets an error and runs nothing (S3.3). |
| `cow_keeps_parent` | A path the child did not change keeps the parent's content (workspace 4). |
| `cow_takes_child` | A path only the child changed gets the child's content (workspace 4). |
| `cow_conflict_reported` | A path both changed to different contents keeps the parent's content and is reported as a conflict: no change is lost in silence (workspace 4, 5). |
| `cow_conflict_is_real` | A conflict is real: both changed the path, to different contents (workspace 4). |

Code: `eukhe-core/src/kernel/manager/frames.rs` (`FrameSplitter`,
`Gate::admit`, `Admission`, `Refusal`, `ProtocolFault`, the limits);
`kernel/manager/startup.rs` `wire_child` (the stdout reader) and
`do_start` (the launch of each transport);
`kernel/manager/host_requests.rs` (`start_host_request`,
`send_host_reply`, the `fs.*` path map); `kernel/transport.rs`
(`KernelTransport`, `KernelWrapper::launch`, `PathMap`);
`kernel/manager/teardown.rs` (`OrphanReap`); `kernel/manager/mod.rs`
(`remote_call`, `RemoteCallError`); `kernel/shared.rs`
(`HostRequestHandlers::serves`, `KernelHostDispatch::serves`);
`durable/rlm/kernels.rs` (`RegistryDispatch`, the `kernelTransport`
setting); `durable/rlm/remote.rs` (`remote.register`, the `remote/<name>`
tools); `eukhe-runtime/src/rlm/remote.py` (`remote`) and `repl.py`
(`_handle_call`, the stdin owner); `eukhe-core/src/child_workspace/`
(`ChildWorkspace`: `create`, `hand_back`; `merge.rs` `merge1`;
`files.rs`: the listing, the clone, the one-rename replace);
`durable/children/` (the `workspace` kwarg, `RlmSubagentHost::hand_back`,
`HandbackOutcome` on the row and the report);
`eukhe-daemon/src/rlm_children/` (the workspace at the spawn,
`hand_back`, `delete`); `eukhe-runtime/src/rlm/__init__.py` (`spawn`).

Ties: two bridge tests compare transcripts with `bend/bridge_sandbox.bend`
byte for byte.

- `kernel::manager::frames::bridge::the_rust_frame_gate_equals_the_bend_model`
  writes 200 generated streams of host-request frames (ids, lengths,
  kinds) as the runtime does, cuts each into reads of random sizes, and
  prints the gate's reply to each frame and the frames it served. The
  scenarios reach every rule: served, oversized, a kind not served, and a
  frame exactly at the limit.
- `child_workspace::bridge::the_rust_hand_back_equals_the_bend_model`
  writes 200 generated parent, base and child file maps as real
  directories, runs the hand-back, and prints the parent's files and the
  conflicts. The scenarios reach every rule: kept, taken, a removal
  taken, the same change, a conflict, and a conflict with a removal.

Regression tests: `kernel_protocol_frame_caps` (an oversized host
request, an unserved type and a served one each get one reply on a real
child, and the session keeps working; an oversized line without a
header lands in repair); `kernel::manager::frames::tests`
(`a_repeated_id_of_a_request_in_flight_gets_a_duplicate_reply_and_no_handler`);
`eukhe-runtime/test/test_repl.py`
(`test_host_duplicate_reply_does_not_settle_the_request_in_flight`);
`child_workspace::tests` (the copy leaves ignored files out; the
hand-back; a hand-back cut by a crash runs again to the same result;
`a_hand_back_after_a_crash_removes_the_copy_the_crash_left_beside_a_path`;
`a_path_the_parent_holds_as_a_directory_or_under_a_file_is_a_conflict`);
the children and daemon workspace tests (`rlm_workspace_e2e`
`a_child_still_writing_at_its_end_stops_before_its_hand_back`: a child
thread that still writes at the end writes nothing after the hand-back);
`kernel::transport::tests` (the
path map both ways, the `fs.*` request and reply maps and refusals,
`fs_requests_reject_a_symlink_in_a_mount_that_points_out_of_every_mount`,
the setting, the launch argv and environment); `kernel_transport` (the real
stub under a fake wrapper, `setsid -w sh -c 'exec "$@"'`, in a sandbox
directory mapped to another host directory: the cwd, the environment,
an `fs.read` with host paths in and sandbox paths out, the typed
refusal, the kill through the closed stdin); `kernel_remote` (register,
call, a raising, unknown and hanging function, a NaN result and wrong
arguments to an async function, then cells and calls still work; a
kernel that exits during a call is unreachable);
`eukhe-runtime/test/test_remote.py` (the schema, the `call`
request, `test_a_nan_result_and_bad_async_arguments_answer_typed_errors`,
the stdin owner). Not modelled: the order of the
replies of accepted requests (handlers end in any order; the kernel
matches by id), the duplicate-id refusal and its `duplicate` reply (the
model's frames have distinct ids, and the bridge's streams too),
directories and symlinks in the hand-back (the model's
paths are flat files), the transport and `@remote` (the tests above tie
them).

### S4. Settings as console variables

Each setting is a console variable (a cvar). One table declares each cvar
once: its id, its type, its scope, two flags and its default. The id is
the dotted path of the key in `settings.json` (`retry.enabled`).

1. The registry holds each id once. A second declaration of an id, or a
   default that does not have the type of its cvar, stops eukhe at
   startup (`RegistryError`).
2. The scope is Global or Local. A Global cvar has one value for every
   agent: only the global config sets it. A Local cvar can have a
   different value in each agent.
3. `persist`: an agent can write its sets of the cvar to its cfg.
   `replicate`: clients see the value of the cvar.

The value of a cvar comes from layers. A higher layer wins:

```text
default < config < each agent of the family, root first:
                   its profile < its own sets
```

- The config is `settings.json` (global, then project) and then
  `config.cfg` (global `<agent dir>/config.cfg`, then project
  `.eukhe/config.cfg`). The project files obey the project trust rules
  of `settings.json`. A project file never sets a Global cvar.
- The profile of a subagent is `subagent.cfg`, then
  `agents/<name>.cfg` for a named agent. The root session is the agent
  `main`.
- The sets of an agent are its runtime sets (`/set`, `/toggle`, the
  session switches). They are session state: the conversation document
  `eukhe.cvar.agent`, committed on each change. So the state tree shows
  them, and a rewind or a fork restores them.

In each layer, the last valid set of a cvar wins. A set is valid when its
cvar is declared and its value has the type of the cvar. In a profile or
an agent's sets, the cvar must also be Local. A set that is not valid is
rejected with a typed error (`CvarError`): `Undeclared`, `BadValue`,
`Global`, `NotBool`.

A subagent starts from the family of its parent: the spawn carries the
parent's layers. Its own profile and sets go on top of them.

The session switches (transport, steering mode, follow-up mode, auto
retry, auto compaction, service tier) are sets of the session's own
agent. They do not change another session. A session cannot set a Global
cvar: `/set --global` writes it to the global `config.cfg`. A `toggle`
in `/set --global` flips the value of the global layer only (the global
`settings.json`, then the global `config.cfg`). A project file never
changes what it flips. The read, the change and the write of a cfg file
hold the lock of the file, so two sessions that write at the same time
do not lose a set. A cfg file that exists but eukhe cannot read is a
settings error, and eukhe does not write it. The errors of a profile
file and of an alias in the agent state that does not parse are
settings errors too. The `eukhe.settings` service shows the settings
errors of a session as an `eukhe.settings_error` row of its main
conversation (display-only: the model does not see it). It shows the
errors at open, and after a reload it shows each new error. It shows
each distinct error one time for each session that eukhe opens.

The command language is the same in the cfg files, in the `/set` slash
command family and in key binds. A line is a list of commands, separated
by `;`. A word in double quotes keeps its spaces.

| Command | Does |
| --- | --- |
| `set <id> <value>` | Sets the cvar. |
| `toggle <id>` | Sets a Bool cvar to the opposite of its value in the agent, with the values the agent inherits. |
| `alias <name> "<cmds>"` | Gives a name to a list of commands. |
| `bind <key> "<cmds>"` | Gives the commands that a key press runs. |
| `action <id>` | Runs a built-in client action (in a bind). |
| `<name>` | Runs the alias `<name>`. |

4. An expansion replaces each run of an alias with its commands. It
   nests at most one level per alias of the table and one more. A deeper
   nest repeats an alias, so it is a cycle (`ExpandError::Cycle`). A run
   of an alias that does not exist is `ExpandError::Unknown`. An
   expansion that fails runs nothing.
5. The key binds are in `<agent dir>/binds.cfg`. The first bind of a key
   wins: the user's binds come before the default binds. A key with no
   bind runs nothing; an empty bind (`bind <key> ""`) turns off a
   default. The default actions that share a key share one bind; the
   screen that gets the key runs its own action. A key press sends its
   `set`, `toggle` and `alias` commands to the session and runs its
   `action` commands in the client. eukhe writes `binds.cfg` one time
   from `keybindings.json` when `binds.cfg` does not exist; the binds it
   writes give each key the actions that `keybindings.json` gave it. A
   `binds.cfg` that eukhe cannot read, or an import that eukhe cannot
   write, shows a warning at startup and at `/reload`.
6. `/cvar save` writes the agent's sets of `persist` cvars to its
   `agents/<name>.cfg`. Read back as the profile, they give the same
   values.

Model: `bend/cvar.bend` (`registry`, `value`, `written`, `toggle`,
`expand`, `press`). Laws: `LAWS.bend` section (S4). Proofs:
`bend/proof_cvar.bend`. Every input is free: any declarations (with
duplicate ids and wrong defaults), any config, any family of agents with
any profiles and sets (wrong types, Global cvars, undeclared ids), any
alias table and any binds.

| Law | Says |
| --- | --- |
| `cvar_registry_unique` | The registry holds each id once (S4.1). |
| `cvar_registry_typed` | Each default of the registry has its type (S4.1). |
| `cvar_value_typed` | Each value has the type of its cvar in each agent; an undeclared cvar has no value. |
| `cvar_inherits` | A subagent with no profile and no sets has its parent's values. |
| `cvar_set_wins` | The last valid set of a subagent wins over its parent's value. |
| `cvar_global_uniform` | A Global cvar has one value in each agent: the config on the default (S4.2). |
| `cvar_written_flagged` | An agent writes to its cfg only `persist` cvars and replicates only `replicate` cvars (S4.3). |
| `cvar_persist_roundtrip` | The written cfg, read back as the profile, gives the same value of each persisting cvar (S4.6). |
| `cvar_toggle_twice` | Two toggles give back the value. |
| `alias_expands_fully` | An expansion leaves no alias to run, or it reports a cycle or an unknown alias (S4.4). |
| `alias_self_cycle` | An alias that runs itself is a cycle (S4.4). |
| `alias_unknown_reported` | A run of an alias that does not exist is reported (S4.4). |
| `alias_runs_body` | An alias of plain commands runs exactly its commands (S4.4). |
| `bind_press_plain` | A key press runs only plain commands (S4.5). |
| `bind_unbound_runs_nothing` | A key with no bind runs nothing (S4.5). |
| `bind_first_wins` | A key press runs the commands of the first bind of the key (S4.5). |

Code: `eukhe-types/src/cvar.rs` (the command language: `parse_list`,
`parse_script`, `Aliases`, `expand`, `Binds::press`);
`eukhe-core/src/settings/cvar.rs` (`Registry`, `Cvars::value`,
`Cvars::execute`, `Sets::written`, `document_sets`) and
`settings/cvar/table.rs` (the declarations); `settings/cfg.rs` (the
config layer: `settings.json`, then the `config.cfg` files under the
trust rules); `settings/manager.rs` and `settings/getters.rs` (the
getters, all through `Cvars`); `eukhe-core/src/durable/cvar_agent.rs` (the
session's agent: `CvarAgent`, the `eukhe.cvar.agent` document,
`run_cvar_line`, `save_agent_cfg`) and `durable/settings.rs`
(`EukheSettings`: the family of the session over its config). The daemon
commands `cvar { line, global }` and `cvar_save` run them
(`eukhe-daemon/src/setting_switches.rs`); a refused command answers its
`CvarError` with `data: { kind, id?, message }`. A spawn carries the parent's
family in the create config (`cvarFamily`). The TUI sends `/set`,
`/toggle`, `/alias` and `/cvar` as `cvar` lines
(`eukhe-tui/src/session_ui/cvar.rs`).

Ties: the bridge test
`settings::cvar::bridge::the_rust_cvars_equal_the_bend_model` compares
transcripts with `bend/bridge_cvar.bend` byte for byte. It runs 300
generated scenarios: registries (with duplicate ids and wrong
defaults), values over a config and a family (wrong types, Global
cvars, undeclared ids, profiles and sets), toggles of the last agent of
a family (a subagent toggles a value that it inherits), the written sets
(`persist` and `replicate`), expansions (cycles, unknown aliases) and
key presses. The scenarios reach every rule.

Regression tests: `a_switch_changes_only_its_own_session` (daemon: two
workers over one agent dir; the switches of one do not change the other
or `settings.json`); `a_setter_never_clobbers_a_global_settings_file_that_failed_to_parse`
(a setter refuses to write over a `settings.json` that did not parse);
`cvar_rejects_a_global_cvar_from_a_session`;
`a_subagent_inherits_its_parents_family_under_its_profile`;
`a_fork_starts_from_the_agent_state_at_its_fork_point`;
`an_unreadable_cfg_file_is_reported_and_never_overwritten`;
`concurrent_global_sets_both_land`;
`a_global_toggle_flips_the_global_value_not_the_projects`;
`profile_and_agent_alias_errors_reach_the_manager`;
`settings_errors_show_as_a_row_of_the_session`;
`unreadable_binds_cfg_and_failed_import_are_warnings`; the
`keybindings::tests` of the `binds.cfg` import and of the presses.

### S5. The Director stack

After each final answer, the agent loop asks a stack of Directors what to
do. A Director is one layer of the stack. A layer has a kind and a
budget: the loop steps that it can still ask for. The kinds are the goal,
the autonomous run, a reminder, and a forced tool call.

1. The top layer decides first. Each layer gives one verdict:
   - `Defer`: the next layer down decides. The layer stays.
   - `Again`: the loop continues. This costs the layer 1 unit of its
     budget. A layer with no budget yields.
   - `Yield`: the loop stops and gives control back to the user.
   - `Stack{l}`: the layer puts `l` on top of itself, and the loop
     continues. This costs 1 unit of budget. A layer with no budget
     yields. A push needs room in the full stack: the layers above the
     layer (also the layers that deferred or left), the layer, and the
     layers below must be fewer than the cap. With no room, the loop
     fails.
   - `Leave`: the layer removes itself. The next layer down decides.
   - `Abort`: the loop stops with a failure.
2. When no layer decides, the loop gives control back to the user.
3. The loop of one run has a global budget of steps. Each continuation
   costs 1 step. When no step is left, a continuation yields.
4. The verdict of each kind comes from the session state:
   - Goal: an active goal mints a continuation (`Again`), with the
     no-progress backoff, or refuses it at the no-progress cap (`Yield`).
     A paused, budget-limited, complete, or failed goal yields. A cleared
     goal leaves.
   - Autonomous: it defers while a goal drives continuations, so the goal
     keeps its priority. A disabled run leaves. Else its gates and limits
     continue the run (`Again`) or stop it (`Yield`).
   - Reminder: its text goes first in the continuation of the step. Then
     it leaves. When the step does not continue (no layer below
     continues, or no step is left), the reminder defers: it stays on the
     stack until a continuation comes. A reminder never makes its own
     continuation, so it waits for the goal or the autonomous run.
   - Forced tool call: each request forces its tool (`stream.forceTool`,
     S6) until a response calls the tool. Then the layer leaves at the next
     final answer. Each response to a forced request without the call is
     a miss. The miss after the `tries` retries fails the generation with
     `ForcedToolError::NotCalled` (S6.3), with the real number of
     requests. That miss removes the layer and appends a display row with
     the error (`eukhe.director`, not in the model context) in one commit,
     so the next request is not forced. When a run ends before a request
     forced the tool, the layer continues the run (`Again`) while it has
     budget. The continuation only names the forced call; the soft prompt
     of the forced request asks for the call. With no budget, the layer
     aborts with `ForcedToolError::NotCalled` and the same display row.
5. A step evaluates the layers from the top until one decides. The
   autonomous gates run before the commit of the step. The step commits
   the stack, the goal and autonomous changes, the goal context row, and
   its decision in one commit. A rerun of the same generation repeats the
   decision.
6. A run that has a new first input starts a new loop: the global budget
   (`directors.maxSteps`, default 200) comes back, the goal layer gets that
   budget, and the autonomous layer gets its remaining continuations
   (`autonomous.maxContinuations` minus the used ones). The goal and the
   autonomous run come on the stack (the goal above the autonomous run)
   when they drive continuations and have no layer. They go below the
   pushed layers (reminders and forced calls), so the pushed layers decide
   first. `directors.stackCap` (default 8) caps the pushed layers only. The
   stack keeps 2 more places, one for the goal and one for the autonomous
   run, so these always have room: a stack holds at most
   `directors.stackCap + 2` layers, and each decision gets that cap. A
   push past the cap is refused with an error. With no layer, a final
   answer writes nothing.
7. Reminders and forced calls come on the stack from these entry points:
   the `/remind <text>` and `/force <tool> [--tries <n>]` session slash
   commands (the TUI sends them through the daemon), and the kernel host
   request `directors.push` (`goal.remind(text)` and
   `goal.force_tool(tool, tries=1)` in the Python REPL). A forced call
   gets 1 unit of budget and `tries` 1 when not given.
8. The stack is the conversation document `eukhe.directors`. It is
   rewindable: a fork or a branch move starts from the stack as of its
   fork entry, so a rewind removes the Directors added after that entry
   and brings back the ones removed. A resume reads the stored stack.
   The document is a node of the state tree (S1), under its conversation.

Model: `bend/director.bend`. Laws: `LAWS.bend` section (S5). Proofs:
`bend/proof_director.bend`. Every verdict is free: each layer of each
step says what the adversary picks.

| Law | Says |
| --- | --- |
| `dir_stack_bounded` | A decision never grows the stack past its cap (S5.1). |
| `dir_loop_stack_bounded` | So the loop never does, whatever its steps (S5.1). |
| `dir_loop_ends` | The loop ends (gives control back or fails) after at most n + 1 steps, with n its global budget, whatever every layer says (S5.3). |
| `dir_end_is_final` | An ended loop stays as it ended (S5.3). |
| `dir_encode_sound` | The stack in the tree is a sound tree (S5.8). |
| `dir_resume_restores` | A resume reads back the stack that the tree holds, exactly (S5.8). |
| `dir_rewind_restores` | A rewind of a sound tree to the tree of a stack restores that stack, exactly (S5.8). |

Code: `eukhe-core/src/durable/directors/stack.rs` `decide`, `Loop::tick`,
`Layer`, `LayerKind`, `Verdict`; `directors/mod.rs` `DIRECTORS_DOC`,
`DirectorState`, `DirectorLimits` (`bound`), `push_director`,
`DIRECTOR_NOTICE_CUSTOM_TYPE`; `durable/goals/hooks.rs` (the `on_yield`
step: `begin`, `judge`, `commit_step`; the forced tool of
`before_request`; the call or the miss of `after_response`,
`mark_forced_response`); `durable/goals/host.rs` (`directors.push`);
`durable/session_commands.rs` (`/remind`, `/force`);
`skills/goal/src/goal/__init__.py` (`remind`, `force_tool`);
`eukhe-durable/src/harness/generation.rs` (the `before_request` hooks may
set the forced tool of a request, `RequestMessages::force_tool`);
`eukhe-core/src/settings` `directors`.

Tie: the bridge test
`durable::directors::bridge::the_rust_director_stack_equals_the_bend_model`
runs `decide`, `Loop::tick`, and the persisted `eukhe.directors` value
against `bend/bridge_director.bend` on 300 generated scenarios (stacks,
verdict lists per step, caps, global budgets; the model's `decide`,
`tick`, `run`, `encode`, and `decode`), and compares the transcripts byte
for byte. The scenarios reach every rule of the model (a push with room,
a push that fits only the layers below, a full stack, no budget, a
leave, all layers defer, no step left, a tick after the end). Regression
tests: `durable::directors::tests` (the goal layer until the goal
completes, the global budget, a reminder, a reminder that waits on the
stack for a continuation, a forced tool call, a forced call that is never
made and a next run that is not forced, the goal on a full stack, the
stack after a reopen and in a fork); `durable::session_commands::tests`
(`/remind` and `/force` on the stack, a `/force` that fails once);
`durable::goals::tests`. Not modelled: the map from the session state to
the verdicts (S5.4), `begin` (S5.6), the reminder that defers when no
continuation follows, and the kind data of a layer (the model keeps a
number for the kind). Their tests tie them.

### S6. The inference layer

The inference layer is between the harness and the wire APIs. It decides
what a request may ask of a provider.

1. The quirks rulebook gives the settings of a model family, a model, and
   a host as data. A rule has a layer, a target id of that layer, and
   directives with values. The compiler rejects an unknown directive, a
   value of the wrong type, and two rules of one layer and target that
   give one directive different values. A lookup takes the rule of the
   highest layer that applies: host over model over family. When no rule
   applies, the answer is Unknown. The rulebook does not guess. The wire
   API applies its own default, and the explicit `model.compat` wins over
   both. The order of the rules changes no answer.
2. A model names one target per layer. The family is the one family
   whose pattern matches the model id (or the id and name). Two families
   that match one model are an error (`QuirksError::FamilyOverlap`). No
   family wins by its id or its order. The test of the shipped rulebook
   rejects two families that match one model of the compiled catalog.
   A model out of the catalog that two families match names no family:
   each family directive is then Unknown, and the log shows the error
   one time for each model id. The model is the model id. The host is
   the host that names the wire API (an API that only one host speaks),
   else the host that names the provider id, else the host with the
   longest URL fragment in the base URL (ties: the smaller host id). A
   model names one host only: the signals do not combine. For example,
   the provider `openrouter` with a loopback base URL (a local proxy)
   gets the settings of the `openrouter` host, not those of the
   `loopback` host. Before the rulebook, the code combined the provider
   and URL checks. The host `openrouter` (provider match) gives
   Anthropic-format `cache_control` marks to `anthropic/` models. The
   host `openrouter-url` (a custom provider with an openrouter.ai base
   URL) gives the other OpenRouter settings, but no marks.
3. A forced tool call names a tool and a count of retries. Every request
   of the call ends with a soft prompt that names the tool. The first
   request sets the native forced choice only when the provider supports
   it and it is free (it costs no prompt-cache invalidation). Each retry
   sets it when the provider supports it. The support is calculated for
   each request (`maps_forced_tool_choice`), with the predicate that the
   wire API uses. Under manual extended thinking, Anthropic and Claude on
   Bedrock reject a forced choice, so the request has no support: no
   attempt escalates to a flag that is not sent. A wire API that gets a
   forced choice under manual extended thinking removes it and logs a
   warning. A reply without the call starts a retry while retries
   remain. After the retries, the generation fails with
   `ForcedToolError::NotCalled`, which names the tool. When no tool is
   forced, nothing changes.
4. A provider takes at most `strict_cap` strict tool schemas per request.
   The tools of highest `priority` get them (default `0`: all equal; of
   equal tools, the earlier one first). The other tools are loose: the
   client validates and repairs their arguments. No tool is dropped. A
   tool that requires a strict schema and is past the cap is an error.
5. The repetition guard reads the text and thinking deltas of every
   stream. A chunk is one complete, non-blank output line. A line longer
   than 4096 bytes (`MAX_CHUNK_BYTES`) ends a chunk at that length, on a
   character boundary; the remaining text starts the next chunk. Thus a
   loop with no newline (`abab…`) is also cut, and the guard keeps at
   most one chunk in memory for each block. When one chunk comes `k`
   times in a row (setting `retry.provider.streamRepeatLimit`, default
   64), the guard aborts the request. The stream then ends with the
   retryable `stream_repeating` failure, which the harness treats like a
   stall. A stream that never repeats a chunk `k` times in a row is not
   cut.
6. Compaction starts on the background path when the context is more
   than the threshold: the limit (`contextWindow - reserveTokens`) less a
   margin (`BackgroundMargin`). The eukhe session sets the margin to 10%
   of the context window (`eukhe-core`); the default of the harness
   library is 32,768 tokens. A context more than the limit blocks the
   request until compaction ends. A background compaction that ends
   during a run places its summary at the run's next boundary; its wire
   `compaction_end` goes out then, with that summary, or as a skip when
   the summary went stale behind a later compaction. The queued summary
   stays after a run end (an aborted run keeps its queued writes). When
   the summary write leaves the queue with no settlement, or a snapshot
   replaces the events that could settle it, the `compaction_end` goes
   out as unsuccessful. While a summary is in the queue (not placed, not
   stale), no background compaction starts. The compaction keeps the most
   recent `compaction.keepRecentTokens` of the context (eukhe default
   40,000; system entries count). The kept part is at most half of the
   threshold, so a compaction always has history to summarize. With a
   small context window, the compaction thus keeps less than the setting.

Model: `bend/infer.bend`. Laws: `LAWS.bend` section (S6). Proofs:
`bend/proof_infer.bend`, `bend/proof_quirks.bend`. Every input is free:
any rulebook, query and directive; any replies of the model; any provider
support; any tools; any stream; any context sizes.

| Law | Says |
| --- | --- |
| `quirk_unknown_rejected` | A rulebook with a rule of an unknown directive does not compile (S6.1). |
| `quirk_clash_rejected` | Two rules of one layer, target and directive with different values do not compile (S6.1). |
| `quirk_unknown_when_none` | With no rule that applies, the answer is Unknown (S6.1). |
| `quirk_known_when_some` | A rule that applies always gives an answer (S6.1). |
| `quirk_highest_wins` | In a rulebook that compiles, the rule of the highest layer that applies gives the answer (S6.1). |
| `quirk_order_free` | In a rulebook that compiles, the order of two rules changes no answer (S6.1). |
| `quirk_compile_order_free` | The order of two rules does not change whether the rulebook compiles (S6.1). |
| `force_bounded` | A forced call makes at most `1 + retries` attempts (S6.3). |
| `force_first_flag` | The first attempt sets the native flag only when it is supported and free (S6.3). |
| `force_retry_flag` | Every retry sets the native flag when it is supported (S6.3). |
| `force_reports` | A forced call reports a call exactly when the model called the tool within its attempts (S6.3). |
| `strict_within_cap` | At most `cap` tools get strict schemas (S6.4). |
| `strict_keeps_every_tool` | Every tool is strict or loose, as many times as it was given (S6.4). |
| `strict_by_priority` | Every strict tool has a priority of at least every loose tool (S6.4). |
| `guard_cuts_repeats` | A stream that repeats a chunk `k` times in a row is cut (S6.5). |
| `guard_keeps_others` | A stream that never repeats a chunk `k` times in a row is not cut (S6.5). |
| `compact_starts_early` | When each turn grows the context by at most the margin, compaction starts before any turn over the limit (S6.6). |

Code: `eukhe-ai/src/quirks/mod.rs` (`compile`, `Rules::lookup`,
`Rulebook::query`, `Rulebook::check_catalog`, `Quirks`) and
`quirks/rulebook.json` (the shipped
rules); the resolvers that take the rulebook as their detected input:
`api/openai_completions/compat.rs` `detect_compat`,
`is_custom_qwen_template_model`; `api/anthropic_messages.rs`
`get_anthropic_compat`, `manual_thinking`; `api/openai_responses.rs`
`get_compat`;
`api/azure_openai_responses.rs`, `api/openai_codex_responses/request.rs`,
`api/bedrock_converse_stream.rs` (strict default, `manual_thinking`),
`bedrock_converse_stream/convert.rs` `supports_adaptive_thinking`,
`api/google_shared/stream.rs` (validated function calling),
`api/mistral_conversations/payload.rs`;
`api/constrained_sampling.rs` `strict_budget`, `StrictPlan`;
`eukhe-types/src/pi_ai/tool.rs` `Tool::priority`;
`eukhe-types/src/pi_ai/settings.rs` `ToolChoice` (`Required`,
`Tool(name)`), mapped in every wire API;
`api/simple_options.rs` `maps_forced_tool_choice`;
`eukhe-durable/src/harness/generation/force.rs` (`ForceEscalation`,
`ForceReply`, `Forcing`, `ForcedToolError`, `soft_prompt`) and the option
`ConversationStreamOptions::force_tool`;
`eukhe-ai/src/utils/stream_repeat.rs` (`RepetitionGuard`,
`MAX_CHUNK_BYTES`, `StreamRepeat`), `api/lazy.rs` `watched_lazy_stream`;
`eukhe-durable/src/harness/generation/decide.rs` `threshold_for`,
`types/settings.rs` `BackgroundMargin`;
`eukhe-core/src/durable/settings.rs` (`WindowPercent(10.0)`, the repeat
limit); `eukhe-daemon/src/worker/durable_host/translator.rs`
(`summary_write`, `end_lost_placements`, the held ends at a snapshot).

Tie: the bridge tests
`harness::generation::infer_bridge::the_rust_quirks_rulebook_equals_the_bend_model`
(compile and lookup on generated rulebooks, each also with two rules
swapped, against `bend/bridge_quirks.bend`; the directives are the first
of each value type in `Directive::ALL`, and a query can name no family
or no host) and
`the_rust_inference_units_equal_the_bend_model` (the escalation, the
strict budget, the guard on lines fed in random deltas, and the
compaction threshold, against `bend/bridge_infer.bend`) compare the
transcripts byte for byte. The code compares token counts strictly
(`>`), so for whole token counts the model threshold is the limit less
the margin, plus one. Regression tests: `quirks::tests` (the shipped
rulebook compiles and no two families match one catalog model;
`families_that_overlap_on_a_catalog_model_are_rejected`;
`a_model_two_shipped_families_match_names_no_family`; errors;
precedence; order; host and family queries; the former hand-written
checks), `openai_completions::tests::host_quirks`
(`a_custom_provider_at_openrouter_ai_sends_no_cache_marks`,
`the_openrouter_provider_at_a_loopback_url_keeps_the_openrouter_settings`),
`constrained_sampling::tests`
(`the_strict_budget_keeps_the_highest_priorities_and_the_earlier_of_equals`,
`a_strict_plan_sends_tools_past_the_cap_loose_and_drops_none`),
`generation::force::tests`
(`manual_extended_thinking_has_no_native_forced_choice`), the
`anthropic_forced_tool_choice` test
`the_forced_choice_predicate_matches_the_wire`,
`utils::stream_repeat::tests` (`a_loop_with_no_newline_is_cut_in_bounded_chunks`,
`a_long_line_is_chunked_on_character_boundaries`),
`generation::tests::threshold`, the translator tests
`a_summary_write_that_leaves_the_inbox_unsettled_ends_its_compaction` and
`a_snapshot_ends_the_compactions_whose_end_it_may_have_replaced`, and the
provider wire tests (`cargo test -p eukhe-ai --test providers`). Not
modelled: the query map from a model to its targets (S6.2), the soft
prompt and wire forms of a forced choice, and the split of deltas into
chunks. Their tests tie them.

### S7. The tool surface

The tool surface is what the model can call: the tools of the roster, the
tools behind `dyn`, the internal URLs and the shell.

1. The roster is the list of tools that each request sends. The roster is
   fixed when the session opens, before its first request. After that, the
   harness rejects each change of the roster with the typed error
   `RosterFixed`: an install or uninstall of an extension that changes the
   tools the model sees, a `configure` of `tools`, `modelTools` or
   `extensions`, and an `add_tools` of a tool round. Each request sends
   the same roster, so the prompt cache stays valid.
2. A tool that comes later (the tool of an MCP server, a host tool that
   joins) does not go into the roster. The roster tool `dyn` reaches it.
   `dyn` without `name` lists the dynamic tools. `dyn` with `name` and
   `arguments` runs one. The tool `mcp/<server>/<tool>` is the tool of an
   MCP server that the user configured; the kernel's MCP client runs it.
   A host tool joins with `ToolSurface::join` and leaves with
   `ToolSurface::quit`. A tool that left is not reachable.
3. Each tool schema that the harness sends has the intent parameter `i`
   (optional, first) and a version of 1 or more: the annotation
   `title: "v<n>"` in the schema itself. Every wire API keeps it. The
   session builds every schema at open: it adds `i` when the schema does
   not have it, keeps each declared parameter in its place, and sets the
   declared version, or 1 when there is none. Building a built schema
   changes nothing. `codemode` gets `i` and `v1` in this way.
4. `report_issue` (behind `dyn`) is the AutoQA path. An agent reports a
   tool that failed or did not do what its description says, with the
   arguments `tool` and `description`. The report is stored in the session
   as a display-only row of custom type `eukhe.tool_issue`. The user sees
   the row. The model context does not get it.
5. Internal URLs. The `read` tool (and the kernel `read()`) accepts an
   internal URL `scheme://path` in place of a file path. `repo://<path>`
   reads a file or directory under the workspace root (the working
   directory of the session). `skill://<name>/<path>` reads a file under
   the directory of the skill `name`; `skill://<name>` reads its
   `SKILL.md`. `agent://<name|id>` reads the whole chat of a subagent that
   the conversation started. `memory://` reads the chat view,
   `memory://<id>` reads message `id` whole (with its images), and
   `memory://<id>/<n>` reads line `id+n`. A `repo://` or `skill://` read
   is a normal file read: it has the `[path#TAG]` header, and its lines
   are edit anchors. An unknown scheme gets the rejection `scheme`.
   `mcp://<server>` lists the resources of a server and
   `mcp://<server>/<uri>` reads one (text; a binary part is a note with
   its size and MIME type), bounded like any read. The server must be one
   of the generic MCP servers of the session. `ssh://` gets the rejection
   `scheme`: eukhe has no SSH client. `glob` rejects all schemes; `grep`
   does not find a scheme path.
6. Confinement. A URL path is a list of `/`-separated segments under the
   root of its scheme. `..` goes up one segment; `.` and an empty segment
   do not move. A path that goes above its root gets the rejection
   `escapes`. The path is not clamped to the root. A path that stays under
   its root resolves. After this lexical check, a `repo://` or `skill://`
   read resolves the real path (it follows symlinks) and requires it under
   the real path of the root. A symlink out of the root also gets the
   rejection `escapes`. This guard is against the filesystem; the model
   stays the lexical rule. A plain file path is not confined; this is the
   same as before. Absolute paths and `..` from the working directory
   still read any file. `lexical_normalize` keeps the filesystem rule
   (`/..` is `/`) and is not used for URL paths.
7. The shell and the approval gate. The `bash` tool (`bash@1`, extension
   `eukhe.shell`) is in the roster at open. It runs a script in process
   (crate `eukhe-shell`). It does not start a system shell for each
   script. A script is a list of steps. A step is one simple command.
   Steps join with `;`, a newline, `&&`, `||` and `|`. Each step can have
   redirections (`<`, `>`, `>>`, `2>&1`, `&>`). The shell expands `$NAME`,
   `${NAME}`, `$?`, a leading `~` and the patterns `*`, `?`, `[...]`. The
   shell runs the usual commands itself: `cat`, `ls`, `head`, `tail`,
   `wc`, `echo`, `pwd`, `mkdir`, `rm`, `rmdir`, `touch`, `cp` and `mv`. It
   runs `grep` on the ripgrep engine (`grep-regex`, `grep-searcher`). It
   starts all other commands, and these commands with options it does not
   know, as external processes. Each external process gets its own
   process group and the same environment as a local kernel: the
   environment of the daemon worker, with the session values on top
   (`EUKHE_CODING_AGENT_DIR`, and `EUKHE_CHAT_MEMORY` in a chat-memory
   session). One function (`kernel::manager::local_env` over
   `durable::rlm::session_env`) makes this environment for both. The
   commands of a pipeline run at the same time. OS pipes connect them, and
   the pipe buffer of the kernel limits each pipe. When a command stops,
   its input pipe closes. The command that writes to that pipe then stops
   too: an external process gets SIGPIPE, and a command of the shell stops
   with status 141. Thus `yes | head -n 3` stops. Some scripts use other
   syntax: control flow, functions, subshells, command substitution,
   here-documents or background jobs. Such a script is one `exec` step,
   and `bash -c` runs it. The tool obeys the S2 limits. The output goes
   through the `Truncation` of the call while the steps write it: the
   result keeps the output within the cap, and the `output_bounded`
   diagnostic counts each dropped byte. With the opt-out, the result keeps
   all of the output. A call blocks for the blocking budget
   (`toolBlockingBudgetMs`) at most. A script that runs longer than the
   budget becomes a job (`JobKind::Shell`) in the `JobTable` of the
   session. The call then settles `detached` with the output until that
   time and the job id. The script continues, and a gated step still asks
   the user. When the script ends, it settles its job and sends a
   `JobSettled::Shell` row (`[job-settled job:ID status:S]` and the
   bounded output) through the job-settled wake, the same as a detached
   cell. The kill of the job stops the script and kills the process group
   of each running external process; the job then settles `killed`.
8. Each step has one effect: read, write, exec or net. A table in
   `eukhe-shell` (`effect.rs`) gives the effect from the command name, the
   `git` subcommand and some options. A command that is not in the table
   has the effect exec. A read step only reads. These rules make sure of
   that:
   - A program name with `/` (`./cat`, `bin/stat`, `/usr/bin/rm`) is
     exec. The shell runs that file, whatever its name.
   - A step with an assignment (`PATH=./bin stat f`, `X=1`) is exec, and
     `export` with an operand is exec. The environment can make a reading
     command run another program (`PATH`, `LD_PRELOAD`, `LESSOPEN`,
     `GIT_*`).
   - `git`: before the subcommand, only `-C DIR` and options that set no
     configuration and no program (`--no-pager`, `-P`, the pathspec
     options, `--no-optional-locks`, `--no-replace-objects`) are allowed.
     Any other option (`-c`, `--config-env`, `--exec-path`, `--git-dir`)
     is exec. A read subcommand with `--output` is write. `git grep` with
     `-O` or `--open-files-in-pager` is exec.
   - `sed`: each script must be a known-safe form, else the step is exec.
     A safe script has only the commands `p P d D q Q = n N g G h H x { }`,
     `s` with the flags `g i I m M p` and a number, and `y`. Each command
     can have the addresses `N`, `$` or `/regex/`, and `!`. The allowed
     options are `-n -E -r -s -u -z -e -i` and their long forms. Any other
     option (`-f`) is exec. With `-i` and safe scripts, the step is write.
   - `rg` with `--pre`, `--pre-glob` or `--hostname-bin` is exec.
   - `sort` with `--compress-program` is exec; with `-o` or `--output` it
     is write.
   - `uniq` and `xxd` with two operands are write (the second operand is
     the output file).
   - `find` with `-exec`, `-execdir`, `-ok` or `-okdir` is exec; with
     `-delete`, `-fls`, `-fprint`, `-fprint0` or `-fprintf` it is write.
   - `less` with a `+` command that has `!` or `|` is exec; with `-o`,
     `-O`, `--log-file` or `--LOG-FILE` it is write.
   - `file` with `-C` or `--compile` is write.
   - `tree` is not in the table (`-o` writes a file), so it is exec.

   A long option can be an abbreviation (GNU `getopt_long`). The rules
   accept each prefix of the option name. An option letter in a group of
   short options (`-uo`) counts.

   A redirection to a file changes a read step to a write step. A step
   whose effect is in the auto set runs immediately. The auto set is the
   Local cvar `shell.autoEffects` (S4): a list of effect names, default
   `["read"]`. A name that is not an effect is a typed error when the
   value is set. The cvar is an execution gate, so an untrusted project
   cannot set it. For each other step, the host asks the user before the
   step runs. The worker sends a `shell_approval` frame to the attached
   clients. The first `answer_shell_approval` (approve or deny) is the
   answer. If no client is attached, or if all clients detach, there is no
   answer. No answer is a denial. The shell asks about the steps of a
   pipeline in order before any of them runs. A denial stops the script at
   that step. The steps before it ran, and their changes stay. The denied
   step, the other steps of its pipeline and all later steps do not run.
   The result gives the output and the exit status of each step that ran.
   It also tells how the script ended: finished, exited, or refused at
   step N (`denied` or `unanswered`). Shell state (`cd`, `export`) lasts
   for one call only. The kernel `bash()` in `ipython` is not gated. The
   reason: a cell is arbitrary Python, and Python can start any process
   without `bash()` (`subprocess`, `os.system`). A gate on `bash()` would
   thus not stop an effect; it would only seem to. Also, `bash()` gives a
   live process handle (pid, kill, tail, background notices) that an
   in-process shell cannot give. The `bash` tool is the gated surface.

Model: `bend/tools.bend`. Laws: `LAWS.bend` section (S7). Proofs:
`bend/proof_tools.bend`. Every input is free: any tools that join and
quit, any schemas, any paths, any scripts, any auto set, any answers of
the user.

| Law | Says |
| --- | --- |
| `roster_fixed` | No event changes the roster: tools that join go behind `dyn` (S7.1, S7.2). |
| `roster_sent_fixed` | Every request of a session sends the roster it started with (S7.1). |
| `dyn_reaches_joined` | A tool that joins is reachable through `dyn` (S7.2). |
| `dyn_drops_quit` | A tool that quits is not reachable through `dyn` (S7.2). |
| `schema_has_intent` | Every schema the harness sends has the intent parameter (S7.3). |
| `schema_versioned` | Every schema the harness sends has a version of at least 1 (S7.3). |
| `schema_keeps_params` | The harness keeps every parameter a tool declares (S7.3). |
| `schema_build_idempotent` | Building a built schema changes nothing (S7.3). |
| `path_rejects_escape` | A path that goes above its root is rejected, never clamped (S7.6). |
| `path_resolves_inside` | A path that stays under its root resolves (S7.6). |
| `gate_prefix` | The steps that ran are the first steps of the script, in order (S7.8). |
| `gate_needs_yes` | No more gated steps run than the user approved (S7.8). |
| `gate_deny_stops` | A denial stops the script at the denied step: the steps before it ran, it and every later step did not (S7.8). |
| `gate_finish_runs_all` | A script that finished ran every step (S7.8). |

Code: `eukhe-durable/src/harness/registry.rs` (`Registry::fix_roster`,
`RosterFixed`, `RosterChange`, the checks in `install` and `uninstall`),
`harness/harness/conversation.rs` `Conversation::configure`,
`harness/generation/round.rs` (`add_tools`);
`eukhe-core/src/durable/registry.rs` `create_eukhe_registry` (builds
every schema, then fixes the roster); `durable/tool_contract.rs`
(`parameters`, `build`); `durable/tool_surface/mod.rs` (`ToolSurface`,
the `dyn` tool, `report_issue`); `kernel/manager/mod.rs`
`mcp_tool_call` and the `mcp_call` request of the kernel's MCP lane
(`eukhe-runtime/src/rlm/repl.py`); `eukhe-docs/src/url.rs` (`Url::names`,
the one place that walks a URL path); `eukhe-core/src/durable/shell.rs`
(the `bash` tool and its approval) and the crate `eukhe-shell` (the
in-process shell, `effect.rs`, the gate).

Tie: the bridge test
`durable::tool_surface::bridge::the_rust_tool_surface_equals_the_bend_model`
drives a real registry with its roster fixed, a `ToolSurface` and
`tool_contract::build` against `bend/bridge_tools.bend` (the model `run`,
`step`, `dyn_call` and `build`): sessions with a roster, tools that join
(the registry is also asked to install them) and quit (the registry is
also asked to drop the roster), requests resolved as the Harness resolves
them, and schemas built twice. `bend/bridge_paths.bend` compares
`Url::names` with the model `resolve` and `stays`. `bend/bridge_shell.bend`
compares the gate of `eukhe-shell`
(`run::tests::the_gate_runs_as_its_model`) with the model `exec`.
Regression tests:
`harness::tests::registry::a_fixed_roster_rejects_every_change_of_the_tools_the_model_sees`,
`durable::tool_surface::tests` (an open session over two turns: every
request sends the same roster while a late tool is listed and run through
`dyn`, `report_issue` stores its row, and install and `configure` are
rejected), and the daemon test `dyn_tool_e2e` (a configured stdio MCP
server's tool is listed and called through `dyn`; the transcript holds one
tool loadout). Not modelled: the wire form of the version annotation, the
MCP listing and call through the kernel, and the row of a report. Their
tests tie them.
