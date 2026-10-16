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
