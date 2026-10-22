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
`bend/compactor.bend`. Proofs: `PROOF.bend` section `compactor`. Every law is
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
count. Proofs: `PROOF.bend` section `compactor`. Every law is universal;
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
only the new ticket). Proofs: `PROOF.bend` section `admission`,
`PROOF.bend` section `admission_wait` (H3.4). Every law is universal: the
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
   A reply with a tool call never answers: its calls go to a tool round,
   whatever its text and its stop reason (vLLM, llama.cpp and Ollama send
   the stop reason `stop` with tool calls). A reply that hit the output
   limit (stop reason `length`) runs none of its calls: their arguments
   can be cut. Each call gets a `truncated` result (`Tool X was not run:
   the reply hit the N-token output limit, so its arguments may be cut.
   Make the call again with complete arguments. For large content, write
   a minimal version first, then extend it with edits.`), and the round
   counts (item 2).
2. A run makes at most `maxToolRounds` tool rounds (default 250; `0` takes
   the default). At the cap it ends as failed (`run_limit`), with a
   message that names the cap. A goal or autonomous continuation starts
   a new count: its own caps bound continuations.
3. The loop guard is removed. It failed a run (`run_limit`, a loop) after
   `LOOP_ROUNDS` (6) rounds in a row with the same tool calls and the
   same results. The repeat recovery of H4.8 replaces it: calls that
   would make `REPEAT_CALLS` (5) such rounds in a row do not run. The law
   `run_loop_needs_repeats` is deleted; the law `rec_never_runs_a_repeat`
   replaces it, and it is stronger: no row of the same calls with the
   same results gets to 5 rounds.
4. A provider that answers "deferred" starts a job, and the run polls
   that job until its deadline: the provider's expiry of the job, else
   the window that the request asked for (`15m`, `1h` or `24h`), else 24
   hours (the longest window). At the deadline the run cancels the job,
   then fails (`model_error`, `The model's deferred response was not
   ready by its deadline, N s after the request`). A failed poll does not
   send the request again while the job can run: a retryable failure
   polls the same job again, after the wait of the retry policy and never
   before the server's wait, while the failures in a row are below
   `retry.maxRetries`; any other failure cancels the job, then fails the
   run. A reply that is still deferred sets the failures in a row to 0.
   The checkpoint of a poll keeps the time the request went out, the
   deadline and the failures in a row, so a restart keeps them.
5. A transient error (not noted, for example an overload or a dropped
   connection) spends a retry: at most `retry.maxRetries`, only when the
   retry policy is enabled, after the wait of the retry policy. A noted
   retry spends a note, never a retry (item 7). A stream that stalled
   (no event within `retry.provider.streamIdleTimeoutMs`) is noted: its
   retry goes out at once with a note (`your previous reply produced no
   output for N s ... Reason briefly, then act`) and with two times the
   idle deadline that the stream stalled under, so the same request does
   not stall the same way again.
6. An abort ends the run within one phase: the phase driver races every
   phase handler, so every `before_request` hook and every wait in it,
   against the invocation's cancel signal. A handler that honours the
   signal returns at once; one that does not is dropped after
   `ABORT_GRACE` (3 s).
7. A reply that ends the model's turn (stop reason `stop`, `length` or
   `toolUse`) with no text and no tool call is no answer: for example
   only thinking, or nothing. A text block with only white space is no
   text. Such a reply never ends the run as answered. A `length` stop with
   no answer gets the length recovery of H4.8: its note is a length note.
   `classify` changes
   it to a failed message before it appends it: the stop reason becomes
   `error` and the error message tells the user that the model gave no
   answer (`The model gave no answer: its reply (stop reason stop) has
   no text and no tool call, only N characters of thinking`). The reply
   is then a noted reply, as a stream that the repetition guard cut: it
   is retried with a note while notes are left, else the run fails with
   `model_error` and that text. Noted retries have their own budget:
   `MAX_NOTES` (8) for each generation, not `retry.maxRetries`. A noted
   retry does not read the retry policy (enabled or not, and its
   maximum), and it goes out at once, with no backoff: it is a new
   request, not a transient error. Each note records the noted retries
   of the generation, its own included (`spent`), thus a restart keeps
   the count. A transient retry spends no note, and a noted retry spends
   no retry. A failed message is not in the context of the next
   request. A model decodes the same request in the same way (a model
   that decodes greedily always does), so a retry must not send that
   request again. After a noted reply (no answer, a stream that the
   repetition guard cut as repeating, or a recovery of H4.8), the request
   of the retry ends with a harness note: a user message that names the
   attempt of the retry and the problem, for example `Harness note,
   attempt 2: your previous reply repeated the line "- r/Bitcoin" until
   it was cut. Give the answer again; never list the same item twice.`
   For a cycle
   of lines, the note gives the length of the cycle and its last line.
   For no answer, it says that the reply gave no text and no tool call;
   for a recovery, H4.8 gives its note.
   Each note names its own attempt, thus the request of each retry is
   different from all the requests that the run sent before. After a
   different error (for example an overload or a dropped connection),
   the retry sends the request again, with the note that it had. A
   compaction keeps the note; a new generation and a retry of a forced
   call start without a note. The run sends the note with the request
   only. It does not write the note to the transcript, thus the chat
   does not show the note or keep it as the words of the user. The
   retry does not send the text of the cut reply: that text is the
   loop, and a greedy model that reads its own loop continues it. Also,
   a partial assistant message before a user message is not a valid
   message order for all providers. Under a forced
   tool call, such a reply is a failed reply, not an answer that missed
   the call. Its note alone makes it retried: the reply is not
   a provider stream failure, so no `StreamFailureKind` applies (a
   `stream_drop` diagnostic is not retryable by its kind, and
   `malformed_response` is never retryable), and the stream of the
   reply does not change for other callers. The memory compactor
   counts a thinking-only reply as a try (H1.4), and the compaction
   summary has its own check for empty text.
8. A stuck model gets a recovery, each with a cap: a `length` stop with
   no answer, tool calls leaked as text, the same tool calls with the
   same results round after round (H4.8).

Changed from the first draft: the round count travels in each
generation's input (durable, so a restart keeps it), not in a separate
live-run field; a continuation resets it (item 2).

A deliberate difference from TS pi-durable: TS's `pi.generation` input
is always `{}`; eukhe's carries `{"rounds": {"count"}}` from the second
generation of a run on (the input of an earlier version also has `same`
and `hash`, the counts of the removed loop guard; a read ignores them).
The cross-implementation
fixtures (`eukhe-durable/tests/fixtures/harness_cross/*-resumed*`) were
edited to that one field after TS wrote them; nothing else in them
changed.

Model: `bend/run.bend`. Its live phases are prepare, call (a request or
a poll), compact (an overflow's or a blocking threshold compaction) and
tools; its limits count down (rounds, compactions, retries, notes, polls
left). Each step is one Rust decision: prepare `before_request`, a compaction's
end `after_compaction` (an overflow's needs its entry; a threshold one
fails the run only when it failed, not when it found nothing), a reply
`after_reply` (a message that ends the model's turn first goes through
`Ended::reply`, the model's `Ended.reply`: its calls when it has calls,
whatever its stop reason, else its text, else a noted error; a noted
error spends a note, a transient one a retry), a round's end
`Rounds::finish` then `RoundEnd::reset` (a control stops the run
uncounted; a queued reset ends it only after the round counted, so the
cap comes first). Proofs:
`PROOF.bend` section `run`. The measure `M` orders a run lexicographically
(rounds left, then compactions, then the retries and notes left in the
generation as one budget, then the ms left of the deferred job (a poll
spends 1 ms), then the phase) and
writes that order as one mixed-radix number: every input to a live run
lowers it by at least one, and at the start it is `bound(cfg)`. Every
law is universal (any limits, any inputs).

The requests of a run (`Reqs`, H4.7) go next to its phases. A request is
the version of its logged context and the attempt that its note names
(0: no note). The logged context only grows (a counted round adds its
calls and results, a compaction adds its entry), thus a version names
one context. A request goes out when preparation ends in a call. A
noted reply (`Error{retryable, noted}` with `noted`) cuts the request
and moves the note to the next attempt; a different error keeps the
note. Proofs: `PROOF.bend` section `retry`, by an invariant: each cut
request is from an older context, or from this context with an earlier
attempt and a different note.

| Law | Says |
| --- | --- |
| `run_ends` | After `bound(cfg) = max(cap, 1)·(2 + (retries + notes + 2)·(polls + 2))` inputs, whatever follows, the run has ended (H4.1, H4.4, H4.5, H4.7). |
| `run_end_stays` | An ended run never changes (H4.1). |
| `run_abort_ends_now` | An abort ends a live run as aborted at the next step (H4.6). |
| `run_rounds_capped` | A run that has made `max(cap, 1)` rounds has failed (H4.2). |
| `run_rounds_fail_at_cap` | The round cap fails a run only once it has made exactly `max(cap, 1)` rounds (H4.2). |
| `run_polls_need_defers` | The poll cap fails a run only after `polls + 1` deferred replies in a row: the request's and each of its `polls` polls' (H4.4). |
| `run_no_answer_is_an_error` | A message that ends the model's turn with no text and no tool call never answers: its step is a noted error's, a retry with a note while notes are left, else the run fails on the model (H4.7). |
| `run_calls_never_answer` | A message that ends the model's turn with a tool call never answers: its calls go to the tools phase, whatever its text and its stop reason (H4.1). |
| `run_note_spends_no_retry` | A noted error spends a note, not a retry: retryable or not, it is retried with a note while notes are left, and the retries left stay (H4.5, H4.7). |
| `run_retry_spends_no_note` | A retryable error that is not noted spends a retry, not a note: the notes left stay (H4.5, H4.7). |
| `run_retry_sends_a_new_request` | No request that the run sends is equal to a request that it sent before and had cut: a retry after a cut sends a new request, cut after cut until the notes run out (H4.7). |
| `run_cut_names_the_request` | A noted reply cuts the request that the run sent, and the next request has the note of the next attempt (H4.7). |
| `run_note_is_never_logged` | A note changes what the model reads, never what the run logs: a request logs the same lines as its context with no note (H4.7). |

Each of these breaks fails a proof: no poll cap, no round cap, a cap
that fails a run early, a poll count that a non-deferred reply does not
reset, an ignored abort in the tools phase, a retry that spends neither
a retry nor a note, a noted retry that spends a retry, a transient
retry that spends a note, a reply with no text and no tool call that
answers, a reply with a tool call that answers, a retry after a cut
that keeps the note of the cut request.

Code: `eukhe-durable/src/harness/generation/decide.rs` (`before_request`,
`after_compaction`, `after_reply`, `Step::Note`, `retry_note`,
`Ended::reply`, `Rounds::finish`, `RoundEnd::reset`, `Limits::max_wait`,
`Counts::waited`, `MAX_NOTES`, `Counts::notes`); `generation/note.rs`
(`RetryNote`, its
`spent` and its text); `generation.rs` `prepare` (both decisions,
`compaction_end`, `threshold_compaction`), `classify` (the reply; a
reply with calls goes to the tools phase whatever its stop reason; a
reply that is no answer becomes a failed message; a reply that is no
answer, a stream cut as repeating or a stream that stalled is noted;
then the step and the note of a retry; a noted retry is due at once, a
transient one after `retry_wait`; a failed poll polls the same job
again or cancels it, `generation/deferred.rs` `PollFailure::next`),
`GenerationInput.rounds`, `GenerationCheckpoint::Poll` (`sentAt`,
`deadline`, `failures`), the `note` of each checkpoint but `Tools`,
`request` (a failed hook fails the run; the note is the last user
message before the soft prompt of a forced call), `abort` (every
checkpoint ends aborted); `generation/round.rs` `start_tool_round` (a
`length` reply's calls get `truncated` results), `finish_tool_round`;
`scheduler/execution.rs` `Inner::run` (the race, `ABORT_GRACE`);
`harness/agent.rs` `DEFAULT_MAX_TOOL_ROUNDS`; `eukhe-core/src/settings`
`maxToolRounds`; `eukhe-ai/src/utils/retry.rs` `repeated_lines` (the
period and the line that `stream_repeating_failure` records).

Tie: the bridge test `harness::generation::bridge::the_rust_decisions_equal_the_bend_model`
calls, at each phase, the production decision that phase calls
(`before_request`, `after_compaction`, `Ended::reply`, `after_reply`,
`retry_note`, `Rounds::finish`, `RoundEnd::reset`), keeps the counters
and the note the checkpoints carry, and runs `bend/bridge_run.bend` on
413 scenarios: 401 generated ones (1 with the production limits, 400
with random small ones, notes included; every reply, noted errors and errors
that are not noted, every message that ends the model's turn with or
without text and with or without tool calls, threshold, compaction
result, round end, and abort) and 12 with a cut after each request
until the notes run out (a noted error or a message with no answer).
After each input it compares the request sent or cut (its context
version and the attempt of its note), then the phase and the counts
left (retries, notes, polls, compactions, rounds), byte for byte. Not in
the bridge: the abort itself (the `abort` handler has one outcome; H4.6's race is
`Inner::run`), the run's other failures (no model, a failed request
hook), which only end it, and the retry of a forced call (`bend/infer.bend`
§2), whose kept answer grows the context. Regression tests
(`harness::generation::tests`):
`run_bounds::a_run_that_keeps_calling_tools_fails_at_the_round_cap`,
`an_abort_ends_a_run_stuck_in_a_request_hook`,
`recovery::keeps_the_rounds_a_run_made_across_reopen`,
`fails_a_response_still_deferred_after_its_last_poll`,
`no_answer::a_reply_of_only_thinking_is_retried_and_then_answers`,
`retry_note::a_retry_after_a_repeating_stream_ends_its_request_with_a_note_and_answers`
(a greedy faux model that sends `- r/Bitcoin` 200 times to a request
without a note: the run answers at the first retry),
`a_retry_after_no_answer_ends_its_request_with_a_note_and_answers`,
`every_retry_after_a_cut_sends_a_new_request_until_the_notes_run_out`
(`MAX_NOTES` noted retries, with `retry.maxRetries` at 2),
`no_answer::replies_of_only_thinking_past_the_notes_fail_the_run_with_model_error`,
`a_reply_of_only_thinking_is_retried_with_a_note_when_the_retry_policy_is_disabled`,
`recoveries::a_noted_retry_is_sent_at_once_and_spends_no_retry`,
`a_reply_with_stop_reason_stop_runs_its_tool_calls`,
`no_call_of_a_reply_cut_at_the_output_limit_runs` (H4.1).

#### H4.8. A stuck model gets a recovery, each with a cap

A weaker model can get stuck. It reasons until it hits the output limit,
again and again. It writes its tool calls as text (markup), not as tool
calls. It makes the same tool calls with the same results, round after
round. The harness does not only watch such a model: each of these
replies gets a recovery, as in omp. A recovery runs the calls, retries
with a note that tells the model what to do, keeps the reply as the
answer, or ends the run. Each recovery has a cap: the number of its notes
in a row.

1. The note of a request counts the notes of its recovery in a row
   (`row`). A note of a different cause, an answer, and calls that run
   start a new row (after a tool round, a new generation starts with no
   note). A transient retry sends the note again: it does not change the
   row.
2. A recovery's retry is a noted retry (H4.7): it spends a note of
   `MAX_NOTES`, it does not read the retry policy, and it goes out at
   once. Its request ends with the note of the next attempt, thus it
   never sends the request again. The stuck reply stays in the
   transcript as a failed message with an error text that tells the user
   what went wrong; it is not in the context of the next request.
3. A reply with no tool call has each text block scanned for tool-call
   markup of five families: Hermes and Qwen JSON (`<tool_call>{...}`),
   Qwen3-Coder XML (`<function=x><parameter=k>`), the omp "qwen" form
   (`<tool_calls><x k="v"/>`), the Kimi section tokens, and DeepSeek
   DSML. Markup in quoted code (a fence or an inline code span) is not a
   leak: the model shows the markup in its answer. When every leaked call
   parses and names a tool that the request offered, the harness rebuilds
   the calls: the markup leaves the text, the calls become tool calls,
   and the stop reason becomes `toolUse`. The run then reads them as the
   same calls made as tool calls (the repeat recovery included). Else
   (a section that does not parse, or a call that names no offered tool)
   the leak recovery starts.
4. The rounds in a row of a reply's calls come from the request's
   context, thus a restart keeps them and a failed reply (not in the
   context) never adds to them. Two rounds are the same when they have
   the same calls and the same results. Calls are the same when they
   have the same names and the same canonical arguments (object keys in
   order at every depth, the top-level intent `i` left out), in any
   order. Results are the same when each result has the same content and
   error flag. A round whose results change (a poll of a job that makes
   progress) starts a new row. A user message (a steer, the user's next
   turn) ends the row: the user changed the context. A system message
   does not end it.

| Recovery | Detection | Cap | At the cap | Note | Laws |
| --- | --- | --- | --- | --- | --- |
| Length | A reply with stop reason `length`, no text and no tool call: the model still reasoned when it hit the output limit. | `LENGTH_NOTES` (3) length notes in a row (omp `INCOMPLETE_RECOVERY_MAX_RETRIES`). | The run fails (`model_error`): `The model gave no answer: its reply (stop reason length) has no text and no tool call, only N characters of thinking. The model hit the output limit while it was still reasoning after 3 length notes in a row: use a different model or raise the model's max output tokens`. | `Harness note, attempt {attempt}: your previous reply hit {limit} while it was still reasoning. It gave no text and no tool call, so the harness discarded it with every tool call that it planned. If you plan the whole task again in your reasoning, you hit the same limit. Reason only about the next step, then call its tool. For a large answer (a file, a document, a long text), write a minimal working version first, then extend it with more edits in later turns. Length note {row} of 3.` `{limit}` is `the {tokens}-token output limit`, or `the output limit` when the provider gave no count. | `rec_length_retries_with_a_note`, `rec_length_gives_up` |
| Leak | A reply with no tool call whose text has tool-call markup that the harness cannot rebuild (rule 3). | `LEAK_NOTES` (2) leak notes in a row (omp `MAX_DSML_LEAK_NUDGES`). | The reply answers as text, as it is. | `Harness note, attempt {attempt}: your previous reply wrote a tool call as {markup} markup in its text, and the harness could not read it ({reason}). No tool ran. Make the call again through the tool-calling interface, with its arguments as one JSON object that agrees with the schema of the tool. Do not write a tool call as text. If you need no tool, give the answer as plain text. Leak note {row} of 2.` `{markup}` is `hermes`, `qwen3`, `qwen-xml`, `kimi` or `dsml`. | `rec_leak_rebuilt_is_calls`, `rec_leak_retries_with_a_note`, `rec_leak_stands` |
| Repeat | Tool calls (made or rebuilt, whatever the stop reason) that would make `REPEAT_CALLS` (5) rounds in a row with the same calls and the same results (rule 4; omp `toolCallLoopGuard.threshold`). Such calls do not run. | `REDIRECT_NOTES` (2) redirect notes in a row. | The run fails (`model_error`): `The model made the same tool calls ({names}) with the same results {rounds} times in a row, after 2 redirect notes; the harness did not run them again`. | `Harness note, attempt {attempt}: you made the same tool calls {rounds} times in a row, and they gave the same results each time: {listed}. The harness did not run them again. Do not make these calls with these arguments again in this turn. Use different arguments, use a different tool, or give your answer with what you found. Redirect note {row} of 2.` `{listed}` gives each call as its tool and its canonical arguments, cut to 400 characters (`ARGUMENTS_SHOWN`, omp `ARGUMENT_SUMMARY_LIMIT`). | `rec_calls_run`, `rec_repeat_never_runs`, `rec_repeat_redirects`, `rec_repeat_gives_up`, `rec_user_breaks_the_row` |

The repeat recovery replaces the loop guard of H4.3, and it stops a row
earlier: at most 4 rounds with the same calls and the same results run in
a row, where the loop guard failed a run only after 6. Calls below its cap
always run: the recoveries never stop a call that is not a repeat.

Model: `bend/run.bend`, section Recoveries, with the caps
`RCfg{long, leak, redirect, repeat}` (in production 3, 2, 2 and 5):
`Rec.step` reads one reply
(`Out`: a length stop, leaked calls, calls that ran, another noted
reply, a user message, an answer, any other reply) and gives an act
(`Pass`, `Exec`, `Redo`, `Stand`, `Quit`) and the recoveries after it.
`Act.reply` turns the act into a reply that the H4 steps read: `Redo` is
a noted error, `Exec` calls, `Stand` text, `Quit` an error that is not
noted. Thus every H4 law holds for a run with the recoveries: those laws
hold for every reply. Laws: `LAWS.bend` section `recover`. Proofs:
`PROOF.bend` section `recover`. Every law is universal (any caps, any
replies, any recovery state).

| Law | Says |
| --- | --- |
| `rec_length_retries_with_a_note` | A length stop with no answer, under the cap, is retried with the next length note (H4.8 Length). |
| `rec_length_gives_up` | After `long` length notes in a row, a length stop fails the run (H4.8 Length). |
| `rec_leak_rebuilt_is_calls` | Leaked calls that all parse and name an offered tool are rebuilt: the run reads them as the same calls made as tool calls (H4.8.3). |
| `rec_leak_retries_with_a_note` | Leaked calls that were not rebuilt, under the cap, are retried with the next leak note (H4.8 Leak). |
| `rec_leak_stands` | After `leak` leak notes in a row, the reply answers as text (H4.8 Leak). |
| `rec_calls_run` | Tool calls that make fewer than `repeat` rounds in a row run; when their results change, a new row of 1 starts (H4.8.4). |
| `rec_repeat_never_runs` | Tool calls that would make `repeat` rounds in a row with the same results never run (H4.8 Repeat). |
| `rec_repeat_redirects` | Such a repeat, under the cap, is retried with the next redirect note (H4.8 Repeat). |
| `rec_repeat_gives_up` | After `redirect` redirect notes in a row, a repeat fails the run (H4.8 Repeat). |
| `rec_user_breaks_the_row` | A user message ends the row: after it, no call is a repeat of a call before it (H4.8.4). |
| `rec_notes_capped` | After any replies, the notes of a recovery in a row are at most its cap (H4.8.1). |
| `rec_never_runs_a_repeat` | After any replies, the run has not run the same calls with the same results `max(repeat, 1)` rounds in a row. It replaces `run_loop_needs_repeats` (H4.3). |
| `rec_stuck_gets_help` | A stuck reply (a length stop with no answer, leaked calls, tool calls) always gets an act that does something: its calls run, a retry with a note, an answer, or the end of the run. It never goes on as it is (H4.8). |
| `rec_redo_is_noted` | A recovery's retry is a noted error: its request has the note of the next attempt, so it never sends the request again (H4.8.2, H4.7). |
| `rec_quit_fails` | A recovery at its cap fails the run on the model, at once (H4.8). |

Code: `eukhe-durable/src/harness/generation/decide.rs` (`recover`,
`Stuck`, `Act`, `Caps`, `CAPS`, `LENGTH_NOTES`, `LEAK_NOTES`,
`REDIRECT_NOTES`, `REPEAT_CALLS`, `MAX_NOTES`); `generation/note.rs`
(`NoteCause::Length`, `NoteCause::Leaked`, `NoteCause::Redirect`,
`NoteCause::row`, `Recovery`, `RepeatedCall`, `ARGUMENTS_SHOWN`,
`RetryNote::text`); `generation/repeat.rs` (`canonical_arguments`,
`rounds_in_a_row`); `generation/leak.rs` (`scan`, `Leak`, `Markup`);
`generation.rs` `classify` (the scan of the text, the rebuild of the
leaked calls, the stuck reply, `recover`, the cause of the note and the
error text); `generation/round.rs` `start_tool_round` (the `truncated`
results of a `length` reply, H4.1).

Tie: the bridge test
`harness::generation::recover_bridge::the_rust_recoveries_equal_the_bend_model`
drives `recover`, `rounds_in_a_row` and `retry_note` as `classify` does,
keeps the note of the next request and the context of the run (each
round that ran is a tool-use reply and its results, each answer a text
reply, each user message a user message), changes the intent and the key
order of each call at random (they are no part of a call's identity),
and runs `bend/bridge_recover.bend` on the same 302 scenarios of replies. After each reply
it compares the act, the recovery and row of the next note, and the
rounds in a row that the run ran with the last calls, byte for byte.
Regression tests (`harness::generation`):
`tests::recoveries::a_length_stop_while_reasoning_is_retried_with_a_length_note_and_answers`,
`length_stops_while_reasoning_fail_the_run_after_three_length_notes`,
`the_same_call_with_the_same_results_is_redirected_on_the_fifth_round_and_then_fails`,
`a_hermes_tool_call_leaked_as_text_is_rebuilt_and_runs`,
`a_broken_leaked_tool_call_is_noted_and_then_stands_as_text_after_two_notes`,
`tests::run_bounds::the_same_calls_whose_results_change_keep_running`,
`repeat::tests::counts_the_rounds_with_the_same_calls_and_the_same_results`
(a user message ends the row),
`canonical_arguments_ignore_the_intent_and_the_key_order`, and the
`leak::tests` (`broken_hermes_calls` and the others).

### H5. Every subagent reports back exactly once

1. Every spawned child ends with exactly one end: a report to its parent
   (completed, failed, cancelled, stalled, unreachable), or none when the
   child already replied by an agent message or the parent itself
   cancelled it (the cancel's result is its answer).
2. A child that makes no progress for `subagentStallMs` (default 600 000;
   `0` or unset takes the default) is stopped (its run is aborted) and
   reported as stalled. Progress is new work, not events. The child's
   token is its work (the number of its distinct acts: a tool call with
   its result, by tool name, arguments, result text and error flag; or
   an accepted progress note), plus the tokens of its own unsettled
   children, plus the output its kernel's jobs wrote (the stdout/stderr
   bytes of its cells and the output bytes of its running `bash()`
   handles). So a child that does new work, waits on a busy child of its
   own, or waits on a background job that writes output (a long build) is
   never stalled. A child that loops is stalled: the same calls with the
   same results, retries, answers, streamed text or thinking do not move
   the token (fixed: the token was the session's event sequence, so every
   streamed delta and retry event counted as progress and a looping child
   ran to its own round caps). A job that writes nothing for
   `subagentStallMs` ends as a stall: jobs have no time bound of their
   own.
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
task reads its submission's fate by id. Proofs: `PROOF.bend` section `child`.
Every law is universal.

| Law | Says |
| --- | --- |
| `child_stalls_in_time` | Quiet polls (same token, or failed), at least as many as the ms left, end the watch (H5.2). |
| `child_unreachable_in_time` | Failed polls in a row, as many as the tries left, end the watch (H5.3). |
| `child_clock_bounded` | The clock never grows past full, so the two bounds are at most `subagentStallMs` ms and `CHILD_POLL_FAILURES` polls (H5.2, H5.3). |
| `child_progress_is_not_a_stall` | A poll with a new token continues the watch with a full clock (H5.2). |
| `child_repeat_is_no_work` (`LAWS.bend` section `progress`) | Acts the child did before add no work: a repeat keeps the token (H5.2). |
| `child_loop_is_a_stall` (`LAWS.bend` section `progress`) | Polls of a child whose acts are all acts it did before, at least as many as the ms left, end the watch (H5.2). |
| `child_new_work_is_progress` (`LAWS.bend` section `progress`) | A poll after an act the child never did before continues the watch with a full clock (H5.2). |
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
- `eukhe-core/src/durable/children/work.rs`: `WorkLedger`, the work
  (`work` in `bend/progress.bend`).
- `eukhe-daemon/src/worker/run_outcome.rs`: the progress token in the
  `get_run_outcome` reply (`RlmChildOutcome`): the session's work
  (`work_progress`), with the kernel's job output
  (`ReplKernelManager::job_output_progress`).
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
keeps it), and
`durable::goals::hooks::bridge::the_rust_progress_check_equals_the_bend_model`
(40 scenarios of 60 goal continuations, `bend/bridge_progress.bend`: the
work ledger over transcripts with call ids, words and thinking that are no
work). Regression
tests: `durable::children::tests::watch::a_hung_child_is_stopped_and_reported_stalled`,
`failing_polls_report_the_child_unreachable`,
`a_progressing_child_outlives_the_stall_budget` (a guard: progress is
never a stall), `tests::report_delivery::a_report_withdrawn_as_its_task_aborts_is_delivered_once`
(three stops in a row, each withdrawing the report), daemon
`rlm_children::durable_host::tests::a_live_child_whose_probes_fail_is_a_failed_poll`,
`stopping_a_child_kills_its_worker_once_and_keeps_its_session`, core
`kernel_lifecycle::background_bash_output_moves_the_job_progress` and
`kernel::manager::events::tests::stream_output_moves_the_job_progress`
(a child idle on a long job that writes output is not stalled), daemon
`worker::run_outcome::tests::a_looping_child_keeps_its_progress_token`.

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
`PROOF.bend` section `wait`, `PROOF.bend` section `lease`. Every law is universal.

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

### H7. A failure the harness sees is shown, with its cause

When the harness can tell that something did not work, it tells the user
or the model what and why. It never drops the cause.

1. A summarizer pass (a compaction summary, a branch summary) runs on the
   model of the `auxiliaryModel` setting. When that setting is unset or
   names the session model, the pass runs on the session model and
   nothing is shown. When the setting names another model that the pass
   cannot use, the session model runs the pass, and the session shows a
   row with the selector, the purpose and the reason. The reasons, in the
   order of the checks: `allowedModels` does not include it; the list of
   available models could not be read; no model with a configured key has
   this name; its API key could not be found; the session's model list
   does not include it; its context window is too small for the request.
   The row never holds auth details: they can hold credentials.
2. The row shows once per session for each purpose, selector and reason.
   A selector that cannot be used would otherwise add the same row at each
   compaction. A new selector, purpose or reason is new information, so
   it shows. A reopened session shows it again once. A branch summary's
   row goes to the conversation the user sees after the move (or stays in
   the main conversation when the summary fails or is cancelled).
3. The skill and prompt template loaders report each candidate file that
   does not load: a file or entry that cannot be read, frontmatter that is
   not valid YAML, a skill without a description, an ignore file that
   cannot be read, an ignore rule that is not a glob, a template path that
   does not exist or is no markdown file, and a template that loses a name
   collision. Each diagnostic has the path and the error text. The
   resource snapshot (`get_resource_snapshot`) carries them in
   `diagnostics.skills` and `diagnostics.prompts`.
4. A tool call that a crash or a restart interrupted is not run again
   (unless it is replay-safe). Its result tells the model what happened
   and what to do next: "Tool X was interrupted and may have partially
   run. Check the state it changes (files, processes, jobs) before you run
   it again." (the restart text says "interrupted by a restart").

Laws (`LAWS.bend` section `progress`): `fallback_is_reported` (every key the session
model was put in place of is noticed), `fallback_quiet_when_routed` (a
notice only comes with a substitution), `fallback_quiet_when_unset`,
`fallback_quiet_when_same`; `skill_failure_reported` (every candidate
file is loaded or named by a diagnostic), `skill_loaded_not_failed` (with
distinct paths, no path is both).

Code: `eukhe-core/src/durable/compaction/auxiliary_model.rs`
(`decide_auxiliary_route`, `AuxiliaryNotices`, `show_auxiliary_notice`),
`eukhe-daemon/src/branch_navigation/summary.rs`,
`eukhe-core/src/skills/` (`discovery.rs`, `prompt_templates.rs`,
`frontmatter.rs`), `eukhe-durable/src/harness/tool.rs`
(`INTERRUPTED_NEXT_STEP`).

Tie: the bridge `durable::compaction::auxiliary_model::tests::bridge` runs
the real decision and notices against `bend/bridge_aux_fallback.bend` on
40 sessions of 60 passes; the bridge `skills::bridge` runs the real
loaders over a temp dir of good, unreadable, malformed and incomplete
files against `bend/bridge_skill_load.bend` on 30 scenarios. Regression
tests: `durable::compaction::tests::an_unused_auxiliary_model_shows_a_notice_once`,
`skills::discovery::tests::reports_each_skill_file_and_ignore_rule_that_fails`,
`skills::prompt_templates::tests::reports_each_template_that_fails`,
`harness::tool::tests::recovery::answers_an_unsafe_tool_interrupted_after_intent_with_what_is_durable_only`.

## Phase sections

- [S1. The session tree](state.md#s1-the-session-tree)
- [S2. Jobs and limits](runtime.md#s2-jobs-and-limits)
- [S3. The host and the sandbox](runtime.md#s3-the-host-and-the-sandbox)
- [S4. Settings as console variables](control.md#s4-settings-as-console-variables)
- [S5. The Director stack](control.md#s5-the-director-stack)
- [S6. The inference layer](inference.md#s6-the-inference-layer)
- [S7. The tool surface](tools.md#s7-the-tool-surface)
- [S8. The interface](interface.md#s8-the-interface)
- [S9. Local tiny models](inference.md#s9-local-tiny-models)
- [S10. Reasoning depth](inference.md#s10-reasoning-depth)
- [Local access: the socket dir, file modes and the working dir](runtime.md#local-access-the-socket-dir-file-modes-and-the-working-dir)
