# Harness laws

Liveness spec: each rule holds whatever model, provider or timing do. Each rule has a Bend model, a law in `LAWS.bend`, a proof in `PROOF.bend`, and a Rust tie. A rule whose model is a function runs as the compiled model itself: Bend compiles every `bend/ffi_<area>.bend` entry into `crates/eukhe-bend/c/core.c` (`make bend-core`); Rust calls it through `eukhe-bend` (wire format of `bend/wire.bend`, `crates/eukhe-bend/WIRE.md`), no Rust copy of the rule. A model abstracting Rust code (protocol, schedule) keeps a bridge test (Rust and Bend run the same scenarios, print the same output) or a regression test. Paths start at `crates/`.

## What a law secures, and what it does not

- Law: proven for the Bend model, every input it names.
- Compiled rule: the proven model is the running code; entry laws (`ffi_<area>.bend`) show it reads the request Rust writes and answers the model's result. Trusted: Bend compiler, C shim (`eukhe-bend/c/shim.c`, `src/ffi.rs`), Rust `Writer`/`Reader` (one FFI test checks them against the Bend codec).
- Bridge: Rust makes the model's steps on its finite scenarios.
- Rust deadline (timer, fuel): ends a production wait; the law shows it suffices (no state where nothing happens).
- Not covered: compiler, OS, network.

## The adversary

Free inputs, any value, any order:
- model reply: any length, empty, thinking only, error, none until the deadline;
- provider: up, slow, down, rate limited, auth expired;
- timing: event order, tick count;
- user: new message, abort, any time.

## Rules

### H1. A compactor call always ends with a line that fits

A call builds one chat-memory line (message summary or merge of two lines).

1. At most `TRIES` model calls.
2. Stops early when a follow-up is not shorter than the best reply.
3. Returns 1 to `NODE` bytes. No fit: cuts the shortest reply (no reply: the input) to `NODE` bytes at a character boundary.
4. Empty or thinking-only reply: a try, never a failure; ends the tries.
5. Provider error, or model call past `CALL_DEADLINE` (10 min, incl. slot wait and session-request preemptions): call fails. After `FAILURES` (3) failed calls the node is built from its input cut to `NODE` bytes (no read: the failed call's input). Only its save can fail. Disk failure (input read, line save, cut save) counts no failure; node stays.

Model: `line`, `Pend.after`, fold `Pend.run` in `bend/compactor.bend`. Proofs: `proof/compactor/`. Universal: every input, reply list, try count, outcome sequence.

| Law | Says |
| --- | --- |
| `line_calls_at_most_tries` | ≤ `tries` calls (H1.1). |
| `line_stops_when_not_shorter` | Follow-up not shorter than an over-long reply: ends after 2 calls, that reply cut to `NODE` (H1.2). |
| `line_fits` | Non-empty input, `NODE` ≥ 4 (widest character): 1 to `NODE` bytes, or call failed (H1.3). |
| `line_takes_first_fit` | Line = first read reply that fits (H1.3). |
| `line_empty_is_a_try` | Empty/thinking-only reply ends with input cut to `NODE` (H1.4). |
| `line_error_fails` | Provider error fails the call (H1.5). |
| `fail_cap_builds` | n failures left: built once n+1 calls failed, whatever between (disk errors, stops, saved line) (H1.5). |

Code: `eukhe-core/src/memory/compactor.rs` `build_line` (loop, `CALL_DEADLINE` per call), `Pend::after`; `memory/mod.rs` `TRIES`, `FAILURES`, `CALL_DEADLINE`, `cut`; `memory/service/actor.rs` `Actor::failed` (`Pend::after`; last failure saves input cut), `Command::Built` (returns input), `Actor::source` (node input).

Tie: bridge `memory::compactor::bridge::the_compactor_equals_the_bend_model`: `build_line` on a scripted model vs `bend/bridge_compactor.bend`, 2,000 scenarios (inputs/replies 1 to 3,000 bytes, 1- to 4-byte characters across the cut, empty/thinking-only replies, block-split or space-padded text, errors, too few replies); compares calls and line byte for byte; also every sequence of ≤ 6 failed calls and disk errors through `Pend::after` vs `Pend.after`, failures left after each. Regression: `compactor::tests::failed_replies_fail_and_empty_ones_give_the_input_cut`, `a_follow_up_not_shorter_ends_the_tries`, `over_long_lines_get_the_cut_and_the_shortest_cut_wins`, `a_model_call_past_its_deadline_fails`, `service::tests::a_node_that_keeps_failing_is_built_from_its_input`, `an_empty_reply_still_gives_a_line_that_fits`, `the_failure_cap_reads_nothing` (log moved before last failure: still built; fails with a cap that rereads the message).

### H2. A turn never waits forever for the memory

A turn waits until every line before its message is summarized (gist rule 47).

1. Waiting turn: unbuilt view nodes go first. Wait start stops every running call of an unneeded node (no failure; node requeued), so no merge holds a one-request provider. Needed view-line calls never stop; the queue starts one whenever a job slot is free and such a line has no call.
2. Each pending node is built after bounded counted outcomes (saved line, failed call H1.5); the wait ends.
3. Last guard: `memory.settleTimeoutMs` (default 20 s; `0`/unset = default). On fire the turn proceeds; an unbuilt line shows its input cut to `NODE`. Never an error.

Model: need-first queue `cands.need`, stop `St.wait` in `bend/optchat.bend`; settle in `bend/compactor.bend`: view line `Made` or `Owed{n}` (failures left); measure = Σ `n + 1` over pending. A pending call ends `Built`, `Failed`, `Disk` or `Stopped`; only the first two count. Proofs: `proof/compactor/`. Universal; `need_progress` from an empty chat after any events.

| Law | Says |
| --- | --- |
| `need_first` | During a wait every started node is an unbuilt view line (H2.1). |
| `need_first_running` | From `St.wait` on, every running/started call is for an unbuilt view line (H2.1). |
| `wait_keeps_needed` | `St.wait` stops no unbuilt view line's call (H2.1). |
| `need_progress` | < `jobs` calls running and a view line neither built nor busy: queue starts a node (H2.1). |
| `settle_falls` | Each counted outcome on a pending line lowers the measure (H2.2). |
| `settle_bounded` | Any outcomes, any order (disk errors, stops included): counted hits on pending lines + measure left ≤ start measure (H2.2). |
| `settle_reached` | Measure-many counted hits: every view line built (H2.2). |
| `settle_start` | Wait start measure = `FAILURES` × unbuilt view lines (H2.2). |

Wait bounds:
- Outcomes: `need_first_running` + `need_progress` (failed line busy until retry): `FAILURES` × unbuilt lines counted outcomes settle the view.
- Stops: all waiters wait for the current view; by `wait_keeps_needed` stops never hit a pending line.
- Preemptions: session request preempts compactor request (H3.1); the call re-asks a slot inside one model call (not an outcome). `CALL_DEADLINE` counts waits and preemptions, so endless preemption fails (counted). Each counted outcome within `TRIES` × `CALL_DEADLINE` of call start, plus `RETRY` before a failed line's next call.
- Disk: an ever-failing disk keeps a line pending; uncovered.
- Time: settle deadline (H2.3) ends every wait regardless.

Code: `memory/chat.rs` `Demand`, `Chat::candidates` (`Demand::Turn`: ready merges wait); `memory/service/actor.rs` `Actor::pump` (demand; waking turns starts held merges), `hold_for_turn` (`Chat::hold_for_turn`, abort calls, drop from prefix gate; `Command::Built`/`Started` carry the call number, stopped results ignored; stop keeps failure count), `Actor::failed` (`Pend::after`), `add_view_waiter` (deadline), `Actor::run` (waits ≤ first deadline, owner-thread clock), `expire_waiters`, `deadline_view` (unbuilt lines as input cut); `memory/service.rs` `Memory::settled_render(within)`; `memory/summarizer.rs` `SettingsSummarizer::complete` (preempted request re-asks a slot within `CALL_DEADLINE`); `settings/manager.rs` `get_memory_settle_timeout` (`memory/mod.rs` `SETTLE_TIMEOUT`); `durable/optchat/request.rs` `pin`.

Tie: `memory::chat::bridge` prints the waiting queue (`n=`) after every event: Rust `candidates(Demand::Turn)` vs `cands.need`, every T of every scenario; lagging scenarios start waits (event `6`: `Chat::hold_for_turn` vs `St.wait`). Compactor bridge ties the failure count (H1). Regression: `service::tests::a_waiting_turn_stops_a_merge_that_holds_the_slot` (one-slot provider, silent merge; fails without the stop), `a_turn_gets_the_view_by_its_deadline_when_the_model_never_answers` (real time, owner-thread deadline), `a_node_that_keeps_failing_is_built_from_its_input`, `an_empty_reply_still_gives_a_line_that_fits` (tokio paused time). Not modelled: provider order of running calls (H3).

### H3. A user's request never waits behind background work

1. A session request preempts every compactor request of its provider.
2. Within a class: oldest first.
3. Free slot + eligible request: taken at once (no lost wake-up).
4. Interactive waits only for interactive requests ahead.

Model: `bend/admission.bend`, one provider, per ticket. State: limit, queue limit, per-ticket class and status (`Queued`, `Granted` uncollected, `Held`, `Preempted`, `Ended`) in ticket order. Rust queues = queued entries per class; counters = entry counts. Ops as Rust: admit (either class), waiter poll, permit drop, waiter drop, new limits; only release/drop run the grant loop; admit grants only the new ticket. Proofs: `proof/admission/` (H3.4). Universal: step laws any state/op; history laws any state reachable from a new controller.

| Law | Says |
| --- | --- |
| `admission_preempts` | After an interactive admit no background slot held (H3.1). |
| `admission_background_yields` | Background slot held only while no interactive holds or waits (H3.1). |
| `admission_fifo` | No holder while an older same-class request waits (H3.2). |
| `admission_no_lost_wakeup` | No free slot while interactive waits, or background waits with no interactive holding/waiting (H3.3). |
| `admission_capacity` | Grants only into free slots: held ≤ limit, or ≤ before minus slots the op freed. Lowered limit drains; no grant until held < limit. |
| `admission_interactive_step` | While interactive w waits no op raises `ahead(s, w)` (interactive held + older interactive waiters); freeing an interactive slot (release, leaving granted waiter) lowers it by one (H3.4). |
| `admission_interactive_bound` | w granted after ≤ `ahead(s, w)` interactive releases, whatever background does (H3.4). |
| `admission_ended_stays_ended` | Ended stays ended. |
| `admission_end_twice_changes_nothing` | Re-ending is a no-op: no double release. |
| `admission_every_ticket_ends` | Holder drop (waiter leaves, permit released) ends the ticket: no leak. |

`admission_interactive_bound` rests on `admission_no_lost_wakeup`: waiting w has `ahead(s, w)` ≥ 1, else its slot would be free.

Code: `eukhe-core/src/admission.rs` `ControllerState` (`has_room`, `interactive_busy`, `hold`, `grant_waiters`, `preempt_background`, `release`), `AdmissionController::admit`, `set_limits`, `QueuedPermit::poll` + `Drop`, `ProviderPermit` `Drop`; daemon registry `eukhe-daemon/src/provider_admission.rs` (same controller, every worker). Queues: `BTreeSet<u64>` by ticket (`admission_fifo`: order = ticket order): O(log n) leave; preempted uncollected grant reinserts without sort.

Tie: compiled model, no bridge. `admission/live.rs` `Live`: a `Stepper` of `bend/ffi_admission.bend` holds the live controller (`Live.step` of `bend/admission.bend`, pinned to the H3 model by law `admission_live_step`) in the Bend heap; each op crosses the wire, the reply is the new state (live tickets in ticket order, next ticket). Not modelled: wakers (a grant takes the waker it fires); daemon connection frames.

### H4. Every run ends

Run = one user turn: model calls, tool rounds, retries.

1. Ends answered, aborted or failed. A reply with a tool call never answers; calls go to a tool round whatever text/stop reason (vLLM, llama.cpp, Ollama send `stop` with tool calls). Stop reason `length`: no call runs (arguments may be cut); each gets `truncated` (`Tool X was not run: the reply hit the N-token output limit, so its arguments may be cut. Make the call again with complete arguments. For large content, write a minimal version first, then extend it with edits.`); the round counts (item 2).
2. ≤ `maxToolRounds` rounds (default 250; `0` = default); at the cap fails `run_limit`, message names the cap. Goal/autonomous continuation restarts the count (own caps).
3. No loop guard (was `run_limit` after `LOOP_ROUNDS` (6) same rounds). Replaced by the H4.8 repeat recovery: calls making `REPEAT_CALLS` (5) same-calls-same-results rounds in a row do not run. Law `rec_never_runs_a_repeat` replaces `run_loop_needs_repeats`.
4. "Deferred" answer starts a job, polled until its deadline: provider job expiry, else requested window (`15m`, `1h`, `24h`), else 24 hours. At deadline: cancel job, fail (`model_error`, `The model's deferred response was not ready by its deadline, N s after the request`). Failed poll never resends while the job can run: retryable → same job polled again after the retry-policy wait (never before the server's wait) while failures in a row < `retry.maxRetries`; else cancel job, fail. Still-deferred reply resets failures in a row to 0. Poll checkpoint keeps send time, deadline, failures in a row (survive restart).
5. Transient (non-noted) error, e.g. overload, dropped connection: spends a retry; ≤ `retry.maxRetries`, only if retry policy enabled, after its wait. Noted retry spends a note, never a retry (item 7). Stalled stream (no event within `retry.provider.streamIdleTimeoutMs`) is noted: retried at once with note (`your previous reply produced no output for N s ... Reason briefly, then act`) and twice the idle deadline it stalled under.
6. Abort ends the run within one phase: the driver races each phase handler (every `before_request` hook and its waits) against the cancel signal; non-honouring handler dropped after `ABORT_GRACE` (3 s).
7. Turn-ending reply (stop `stop`, `length`, `toolUse`) with no text and no tool call (thinking only, nothing; whitespace-only text = no text) is no answer; never ends answered. `length` + no answer → H4.8 length recovery (length note).
   - `classify` makes it a failed message before append: stop reason `error`, message `The model gave no answer: its reply (stop reason stop) has no text and no tool call, only N characters of thinking`. Then noted, like a repetition-guard cut: retried with a note while notes last, else fails `model_error` with that text.
   - Note budget: `MAX_NOTES` (8) per generation, not `retry.maxRetries`; ignores retry policy (enabled, max); sent at once, no backoff. Each note records the generation's noted retries incl. itself (`spent`); restart keeps it. Transient retry spends no note; noted retry no retry.
   - Failed message excluded from next context. Same request decodes the same (greedy), so never resend it: after a noted reply (no answer, repetition-guard cut, H4.8 recovery) the retry request ends with a harness note, a user message naming attempt and problem, e.g. `Harness note, attempt 2: your previous reply repeated the line "- r/Bitcoin" until it was cut. Give the answer again; never list the same item twice.` Cycle: note gives cycle length and last line. No answer: says no text and no tool call. Recovery: H4.8 note.
   - Each note names its attempt, so each retry request is new. Other errors (overload, dropped connection) resend with the same note. Compaction keeps the note; new generation and forced-call retry start without.
   - Note goes with the request only, never the transcript (chat neither shows nor keeps it as user words). Cut reply text is not resent (greedy model continues its loop; partial assistant before user message is invalid for some providers).
   - Under a forced tool call: failed reply, not a missed call; retried by its note alone. Not a stream failure: no `StreamFailureKind` (`stream_drop` not retryable by kind, `malformed_response` never); stream unchanged for other callers. Compactor: thinking-only = try (H1.4); compaction summary checks empty text itself.
8. Stuck model recoveries, each capped: `length` stop with no answer, tool calls leaked as text, same calls with same results round after round (H4.8).

Round count rides each generation's input (survives restart); continuation resets it (item 2). TS pi-durable `pi.generation` input is always `{}`; eukhe carries `{"rounds": {"count"}}` from the second generation (old inputs' `same`, `hash` of the removed guard are ignored). Fixtures `eukhe-durable/tests/fixtures/harness_cross/*-resumed*` differ from TS in that field only.

Model: `bend/run.bend`. Phases: prepare, call (request/poll), compact (overflow or blocking threshold), tools; limits count down (rounds, compactions, retries, notes, polls). Steps = Rust decisions:
- prepare: `before_request`;
- compaction end: `after_compaction` (overflow needs its entry; threshold fails only on failure, not on nothing found);
- reply: `after_reply`; turn-ending message via `Ended::reply` (model `Ended.reply`): calls if any, any stop reason; else text; else noted error. Noted spends a note, transient a retry;
- round end: `Rounds::finish`, `RoundEnd::reset` (control stops uncounted; queued reset ends only after the round counted: cap first).

Proofs: `proof/run/`. Measure `M`, lexicographic as one mixed-radix number: rounds left, compactions, retries+notes (one budget per generation), deferred-job ms left (poll = 1 ms), phase. Each live input lowers it ≥ 1; start = `bound(cfg)`. Universal (any limits, inputs).

Requests (`Reqs`, H4.7) sit beside phases: request = logged-context version + note attempt (0: none). Logged context only grows (counted round adds calls/results, compaction its entry): a version names one context. Sent when prepare ends in a call. Noted reply (`Error{retryable, noted}`, `noted`) cuts it, note moves to next attempt; other errors keep the note. Proofs: `proof/run/`; invariant: each cut request is from an older context, or this context with an earlier attempt and different note.

| Law | Says |
| --- | --- |
| `run_ends` | Ended after `bound(cfg) = max(cap, 1)·(2 + (retries + notes + 2)·(polls + 2))` inputs (H4.1, H4.4, H4.5, H4.7). |
| `run_end_stays` | Ended run never changes (H4.1). |
| `run_abort_ends_now` | Abort ends a live run as aborted next step (H4.6). |
| `run_rounds_capped` | `max(cap, 1)` rounds made: failed (H4.2). |
| `run_rounds_fail_at_cap` | Round cap fails only at exactly `max(cap, 1)` rounds (H4.2). |
| `run_polls_need_defers` | Poll cap fails only after `polls + 1` deferred replies in a row (request + `polls` polls) (H4.4). |
| `run_no_answer_is_an_error` | No text, no tool call: noted error, retried with note while notes last, else fails on the model (H4.7). |
| `run_calls_never_answer` | Tool call: never answers; to tools phase whatever text/stop reason (H4.1). |
| `run_note_spends_no_retry` | Noted error (retryable or not) spends a note; retries left unchanged (H4.5, H4.7). |
| `run_retry_spends_no_note` | Retryable non-noted error spends a retry; notes unchanged (H4.5, H4.7). |
| `run_retry_sends_a_new_request` | No sent request equals an earlier cut one, cut after cut until notes run out (H4.7). |
| `run_cut_names_the_request` | Noted reply cuts the sent request; next carries the next attempt's note (H4.7). |
| `run_note_is_never_logged` | Note changes model input only; logged lines equal the note-less context (H4.7). |

Breaks that fail a proof: no poll cap; no round cap; early cap; poll count not reset by a non-deferred reply; abort ignored in tools; retry spending neither retry nor note; noted retry spending a retry; transient retry spending a note; no-text-no-call reply answering; tool-call reply answering; post-cut retry keeping the cut note.

Code: `eukhe-durable/src/harness/generation/decide.rs` (`before_request`, `after_compaction`, `after_reply`, `Step::Note`, `retry_note`, `Ended::reply`, `Rounds::finish`, `RoundEnd::reset`, `Limits::max_wait`, `Counts::waited`, `MAX_NOTES`, `Counts::notes`); `generation/note.rs` (`RetryNote`, `spent`, text); `generation.rs` `prepare` (both decisions, `compaction_end`, `threshold_compaction`), `classify` (calls → tools any stop reason; no answer → failed message; no answer, repeating cut, stall → noted; step and note; noted due at once, transient after `retry_wait`; failed poll repolls or cancels, `generation/deferred.rs` `PollFailure::next`), `GenerationInput.rounds`, `GenerationCheckpoint::Poll` (`sentAt`, `deadline`, `failures`), `note` of every checkpoint but `Tools`, `request` (failed hook fails the run; note = last user message before a forced call's soft prompt), `abort` (every checkpoint ends aborted); `generation/round.rs` `start_tool_round` (`length` calls get `truncated`), `finish_tool_round`; `scheduler/execution.rs` `Inner::run` (race, `ABORT_GRACE`); `harness/agent.rs` `DEFAULT_MAX_TOOL_ROUNDS`; `eukhe-core/src/settings` `maxToolRounds`; `eukhe-ai/src/utils/retry.rs` `repeated_lines` (period and line `stream_repeating_failure` records).

Tie: the running code is the model. `before_request`, `after_compaction`, `Ended::reply`, `after_reply`, `round_end`, `PollFailure::next` call `decide.prepare`, `decide.compact`, `Ended.reply`, `decide.reply`, `decide.round`, `decide.poll` of `bend/run.bend` through the compiled core (`bend/ffi_run.bend`, `generation/entry.rs`). Each decision turns Rust's counters (counting up) into the model's counts left and takes the model's step; `LAWS.bend` (H4.9) proves each equal to the rule `decide.rs` wrote, every input (`run_*_is_the_rust_rule`), counts left lossless (`run_counts_lossless`, `run_rounds_lossless`) and counting down as Rust counts up (`run_*_counts_down`), saturation of Rust's u64s at the wire's largest Nat exact (`run_reply_saturates_the_*`), a failed poll with its time check = the job of `bend/retry.bend` §4 (`run_failed_poll_is_the_job_model`); section `run_ffi` proves the codec. Outside the model: `retry_note` (data: note's attempt and spent = request's + 1); the abort itself (`abort` handler has one outcome; H4.6 race is `Inner::run`); other failures (no model, failed request hook) that only end the run; forced-call retry (`bend/infer.bend` §2, kept answer grows context). Regression (`harness::generation::tests`): `run_bounds::a_run_that_keeps_calling_tools_fails_at_the_round_cap`, `an_abort_ends_a_run_stuck_in_a_request_hook`, `recovery::keeps_the_rounds_a_run_made_across_reopen`, `fails_a_response_still_deferred_after_its_last_poll`, `no_answer::a_reply_of_only_thinking_is_retried_and_then_answers`, `retry_note::a_retry_after_a_repeating_stream_ends_its_request_with_a_note_and_answers` (greedy faux model sends `- r/Bitcoin` 200 times without a note; answers at first retry), `a_retry_after_no_answer_ends_its_request_with_a_note_and_answers`, `every_retry_after_a_cut_sends_a_new_request_until_the_notes_run_out` (`MAX_NOTES` noted retries, `retry.maxRetries` 2), `no_answer::replies_of_only_thinking_past_the_notes_fail_the_run_with_model_error`, `a_reply_of_only_thinking_is_retried_with_a_note_when_the_retry_policy_is_disabled`, `recoveries::a_noted_retry_is_sent_at_once_and_spends_no_retry`, `a_reply_with_stop_reason_stop_runs_its_tool_calls`, `no_call_of_a_reply_cut_at_the_output_limit_runs` (H4.1).

#### H4.8. A stuck model gets a recovery, each with a cap

Stuck: reasoning to the output limit; tool calls as text markup; same calls with same results each round. Recoveries (as omp): run calls, retry with note, keep reply as answer, or end run. Cap = recovery notes in a row.

1. A note counts its recovery's notes in a row (`row`). Other-cause note, answer, or calls that run reset the row (a new generation after a tool round starts note-less). Transient retry resends the note; row unchanged.
2. Recovery retry = noted retry (H4.7): spends a `MAX_NOTES` note, ignores retry policy, sent at once, ends with next attempt's note (never resends). Stuck reply stays in the transcript as a failed message with user-facing error text; excluded from next context.
3. No-tool-call reply: each text block scanned for five markup families: Hermes/Qwen JSON (`<tool_call>{...}`), Qwen3-Coder XML (`<function=x><parameter=k>`), omp "qwen" (`<tool_calls><x k="v"/>`), Kimi section tokens, DeepSeek DSML. Quoted code (fence, inline span) is no leak. All calls parse and name offered tools → rebuilt: markup leaves text, calls become tool calls, stop reason `toolUse`, read as normal calls (repeat recovery included). Else (unparsable section, unoffered tool) → leak recovery.
4. Rounds in a row come from the request context: restart keeps them; failed replies (not in context) never add. Same round = same calls + same results. Same calls = same names + canonical arguments (keys sorted at every depth, top-level intent `i` dropped), any order. Same results = same content and error flag each. Changed results (progressing job poll) start a new row. User message (steer, next turn) ends the row; system message does not.

| Recovery | Detection | Cap | At the cap | Note | Laws |
| --- | --- | --- | --- | --- | --- |
| Length | Stop `length`, no text, no tool call (still reasoning at limit). | `LENGTH_NOTES` (3) in a row (omp `INCOMPLETE_RECOVERY_MAX_RETRIES`). | Fails (`model_error`): `The model gave no answer: its reply (stop reason length) has no text and no tool call, only N characters of thinking. The model hit the output limit while it was still reasoning after 3 length notes in a row: use a different model or raise the model's max output tokens`. | `Harness note, attempt {attempt}: your previous reply hit {limit} while it was still reasoning. It gave no text and no tool call, so the harness discarded it with every tool call that it planned. If you plan the whole task again in your reasoning, you hit the same limit. Reason only about the next step, then call its tool. For a large answer (a file, a document, a long text), write a minimal working version first, then extend it with more edits in later turns. Length note {row} of 3.` `{limit}`: `the {tokens}-token output limit`, or `the output limit` without a provider count. | `rec_length_retries_with_a_note`, `rec_length_gives_up` |
| Leak | No tool call; unrebuildable markup in text (rule 3). | `LEAK_NOTES` (2) in a row (omp `MAX_DSML_LEAK_NUDGES`). | Reply answers as text, unchanged. | `Harness note, attempt {attempt}: your previous reply wrote a tool call as {markup} markup in its text, and the harness could not read it ({reason}). No tool ran. Make the call again through the tool-calling interface, with its arguments as one JSON object that agrees with the schema of the tool. Do not write a tool call as text. If you need no tool, give the answer as plain text. Leak note {row} of 2.` `{markup}`: `hermes`, `qwen3`, `qwen-xml`, `kimi`, `dsml`. | `rec_leak_rebuilt_is_calls`, `rec_leak_retries_with_a_note`, `rec_leak_stands` |
| Repeat | Calls (made or rebuilt, any stop reason) that would make `REPEAT_CALLS` (5) same rounds in a row (rule 4; omp `toolCallLoopGuard.threshold`); not run. | `REDIRECT_NOTES` (2) in a row. | Fails (`model_error`): `The model made the same tool calls ({names}) with the same results {rounds} times in a row, after 2 redirect notes; the harness did not run them again`. | `Harness note, attempt {attempt}: you made the same tool calls {rounds} times in a row, and they gave the same results each time: {listed}. The harness did not run them again. Do not make these calls with these arguments again in this turn. Use different arguments, use a different tool, or give your answer with what you found. Redirect note {row} of 2.` `{listed}`: each call's tool and canonical arguments, cut to 400 characters (`ARGUMENTS_SHOWN`, omp `ARGUMENT_SUMMARY_LIMIT`). | `rec_calls_run`, `rec_repeat_never_runs`, `rec_repeat_redirects`, `rec_repeat_gives_up`, `rec_user_breaks_the_row` |

≤ 4 same rounds run in a row (old H4.3 guard: 6). Non-repeat calls always run.

Model: `bend/run.bend` section Recoveries, caps `RCfg{long, leak, redirect, repeat}` (production 3, 2, 2, 5). `Rec.step` reads one reply (`Out`: length stop, leaked calls, run calls, other noted reply, user message, answer, other) → act (`Pass`, `Exec`, `Redo`, `Stand`, `Quit`) + next recoveries. `Act.reply` maps acts to H4 replies: `Redo` noted error, `Exec` calls, `Stand` text, `Quit` non-noted error; so all H4 laws (true for every reply) hold with recoveries. Laws: `LAWS.bend` section `recover`. Proofs: `proof/run/`. Universal (any caps, replies, state).

| Law | Says |
| --- | --- |
| `rec_length_retries_with_a_note` | No-answer length stop under cap: next length note (H4.8 Length). |
| `rec_length_gives_up` | After `long` length notes in a row: fails (H4.8 Length). |
| `rec_leak_rebuilt_is_calls` | All parse, all offered: rebuilt, read as tool calls (H4.8.3). |
| `rec_leak_retries_with_a_note` | Not rebuilt, under cap: next leak note (H4.8 Leak). |
| `rec_leak_stands` | After `leak` leak notes in a row: answers as text (H4.8 Leak). |
| `rec_calls_run` | < `repeat` rounds in a row: run; changed results start a row of 1 (H4.8.4). |
| `rec_repeat_never_runs` | Would make `repeat` same rounds: never run (H4.8 Repeat). |
| `rec_repeat_redirects` | Under cap: next redirect note (H4.8 Repeat). |
| `rec_repeat_gives_up` | After `redirect` redirect notes in a row: fails (H4.8 Repeat). |
| `rec_user_breaks_the_row` | User message ends the row; no later call repeats an earlier one (H4.8.4). |
| `rec_notes_capped` | Notes in a row ≤ cap (H4.8.1). |
| `rec_never_runs_a_repeat` | Never `max(repeat, 1)` same rounds run in a row. Replaces `run_loop_needs_repeats` (H4.3). |
| `rec_stuck_gets_help` | Stuck reply (no-answer length stop, leaked calls, tool calls) always gets an effective act: calls run, noted retry, answer, or end (H4.8). |
| `rec_redo_is_noted` | Recovery retry = noted error with next attempt's note; never resends (H4.8.2, H4.7). |
| `rec_quit_fails` | At cap: fails on the model at once (H4.8). |

Code: `eukhe-durable/src/harness/generation/decide.rs` (`recover`, `Stuck`, `Act`, `Caps`, `CAPS`, `LENGTH_NOTES`, `LEAK_NOTES`, `REDIRECT_NOTES`, `REPEAT_CALLS`, `MAX_NOTES`); `generation/note.rs` (`NoteCause::Length`, `NoteCause::Leaked`, `NoteCause::Redirect`, `NoteCause::row`, `Recovery`, `RepeatedCall`, `ARGUMENTS_SHOWN`, `RetryNote::text`); `generation/repeat.rs` (`canonical_arguments`, `rounds_in_a_row`); `generation/leak.rs` (`scan`, `Leak`, `Markup`); `generation.rs` `classify` (scan, rebuild, stuck reply, `recover`, note cause, error text); `generation/round.rs` `start_tool_round` (`length` → `truncated`, H4.1).

Tie: `recover` calls `decide.recover` of `bend/run.bend` (recoveries `Rec` reading stuck reply and note row as Rust has them) through the compiled core; `rec_recover_is_the_rust_rule` proves it equal to the rule `decide.rs` wrote, so every `rec_*` law is a law of the running code. `rounds_in_a_row` (hashing of calls and results) stays in Rust, tested in `repeat::tests`. Regression (`harness::generation`): `tests::recoveries::a_length_stop_while_reasoning_is_retried_with_a_length_note_and_answers`, `length_stops_while_reasoning_fail_the_run_after_three_length_notes`, `the_same_call_with_the_same_results_is_redirected_on_the_fifth_round_and_then_fails`, `a_hermes_tool_call_leaked_as_text_is_rebuilt_and_runs`, `a_broken_leaked_tool_call_is_noted_and_then_stands_as_text_after_two_notes`, `tests::run_bounds::the_same_calls_whose_results_change_keep_running`, `repeat::tests::counts_the_rounds_with_the_same_calls_and_the_same_results` (user message ends the row), `canonical_arguments_ignore_the_intent_and_the_key_order`, `leak::tests` (`broken_hermes_calls` etc.).

### H5. Every subagent reports back exactly once

1. Each spawned child has exactly one end: a report (completed, failed, cancelled, stalled, unreachable), or none if it already replied by agent message or the parent cancelled it (cancel result = answer).
2. No progress for `subagentStallMs` (default 600 000; `0`/unset = default): run aborted, reported stalled. Progress = new work, not events. Token = work (distinct acts: tool call + result by name, arguments, result text, error flag; or accepted progress note) + tokens of unsettled own children + kernel job output (cell stdout/stderr bytes, running `bash()` handle output bytes). New work, a busy child, an output-writing job (long build): never stalled. Loops (same calls/results, retries, answers, streamed text, thinking) do not move the token: stalled. A job silent for `subagentStallMs` stalls (jobs have no own time bound).
3. `CHILD_POLL_FAILURES` (5) failed polls in a row while the worker lives or restarts: unreachable. Pause doubles per failure (2 s, 4 s, ... 32 s; ~1 minute), per polling session: reopened parent polls at once (only a poll reveals an interruption while down). Gone worker settles at once (`worker-exited`). Stalled/unreachable: run aborted, agent stopped via the `rlm` kill path (plain kill: worker released, session kept, later prompt wakes it).
4. Delivered once: resend keeps request id; parent drops known ids. Rule: submit; wait until settled; end once placed; resubmit under the next id only once withdrawn (parent abort/close, input withdrawal). ≤ 1 live submission (queued or placed); withdrawal losing to placement leaves it placed; ≤ 1 resubmission per withdrawal. Closing parent admits nothing; report stays owed, reopened session delivers. Aborting the owing task submits nothing: hands the report (same ids, withdrawals so far) to a new report-phase task the abort cannot reach, so every withdrawal, even one racing the abort, gets the next id.

Model: `bend/child.bend`. Clock `W`: no-progress ms left (`left`), failed polls left (`tries`); `look` = one-poll verdict. Task (`St`, `step`) vs adversary: polls (any reading, delay), deliveries/withdrawals of any submission id, parent aborts, closes, reopens, task aborts, deletes, any order. Inbox keeps each submission's fate (queued, withdrawn, placed), read by id. Proofs: `proof/child/`. Universal.

| Law | Says |
| --- | --- |
| `child_stalls_in_time` | Quiet polls (same token or failed) ≥ ms left end the watch (H5.2). |
| `child_unreachable_in_time` | Failed polls in a row = tries left end the watch (H5.3). |
| `child_clock_bounded` | Clock ≤ full: bounds `subagentStallMs` ms, `CHILD_POLL_FAILURES` polls (H5.2, H5.3). |
| `child_progress_is_not_a_stall` | New token: full clock (H5.2). |
| `child_repeat_is_no_work` (`LAWS.bend` section `progress`) | Repeat keeps the token (H5.2). |
| `child_loop_is_a_stall` (`LAWS.bend` section `progress`) | All-repeat polls ≥ ms left end the watch (H5.2). |
| `child_new_work_is_progress` (`LAWS.bend` section `progress`) | Poll after a new act: full clock (H5.2). |
| `child_one_live` | ≤ 1 live submission (H5.4). |
| `child_report_once` | ≤ 1 placed: transcript holds it at most once (H5.4). |
| `child_resubmits_per_abort` | Submissions ≤ 1 + parent aborts, closes, withdrawals (H5.4). |
| `child_delivered_once` | Owed report placed exactly once when the parent reopens, the task takes three steps, and the parent's run places the id then awaited (H5.4). |
| `child_task_call` | Task's call on a poll = watch verdict (`look`) as its report mode acts on it: watch on, report, or settle without report (H5.2-H5.4). |
| `child_silent_never_reports` | Silent task (`ReportMode::Silent`) never reports to its parent. |
| `child_report_move`, `child_report_move_is_owe` | Report phase's move = the one report rule; carried out = model's `owe` (H5.4). |
| `child_abort_rule` | Abort of a watched child: delete owes a cancelled report, cancel owes nothing; an owed report goes on as it was (H5.4). |
| `child_entry_verdict`, `child_entry_move`, `child_entry_abort` (`LAWS.bend` section `core_w6`) | Core's child entry answers, on each request Rust writes, the model's encoded decision. |

Rust (paths from `crates/`); the task's three decisions run as the compiled Bend core (`bend/ffi_child.bend`, through `eukhe-bend`):
- `eukhe-core/src/durable/children/watch.rs`: `verdict` (`verdict` in `bend/child.bend`); checkpoint `Vigil` (quiet ms, failed polls, counting up) as the model's clock (`left`, `tries`, counting down); `CHILD_POLL_FAILURES`.
- `eukhe-core/src/durable/children/task.rs`: `watch` phase checkpoints `Vigil`, skips the pause on a session's first poll (`ChildrenServices.polled`), aborts then stops stuck children (`host.cancel`, `host.stop`), reports `Failed{stalled|unreachable}`; `watched_next` turns the call into the next state; `report` phase follows `report_step` (`owe.next`) on its submission's `Fate`; `abort` hands the report `owed_on_abort` (`cut.ph`) picks to a new task (`ChildTaskInput.owed`, row's `reporter`, awaited by the quiescence barrier).
- `eukhe-core/src/durable/children/work.rs`: `WorkLedger` (`work` in `bend/progress.bend`).
- `eukhe-daemon/src/worker/run_outcome.rs`: token in `get_run_outcome` reply (`RlmChildOutcome`): `work_progress` + `ReplKernelManager::job_output_progress`.
- `eukhe-daemon/src/rlm_children/durable_host.rs` `wait_settled`: failed probe of a live/restarting worker = failed poll (was `Running` forever); `stop` = plain kill.
- `eukhe-core/src/settings`: `subagentStallMs`.

Tie: the decisions are the proven model itself (compiled core); `durable::goals::hooks::bridge::the_rust_progress_check_equals_the_bend_model` (40 × 60 goal continuations, `bend/bridge_progress.bend`: ledger over transcripts with call ids, words, thinking as non-work). Regression: `durable::children::tests::watch::a_hung_child_is_stopped_and_reported_stalled`, `failing_polls_report_the_child_unreachable`, `a_progressing_child_outlives_the_stall_budget` (progress never stalls), `tests::report_delivery::a_report_withdrawn_as_its_task_aborts_is_delivered_once` (three stops in a row, each withdrawing); daemon `rlm_children::durable_host::tests::a_live_child_whose_probes_fail_is_a_failed_poll`, `stopping_a_child_kills_its_worker_once_and_keeps_its_session`; core `kernel_lifecycle::background_bash_output_moves_the_job_progress`, `kernel::manager::events::tests::stream_output_moves_the_job_progress` (idle on output-writing job: not stalled); daemon `worker::run_outcome::tests::a_looping_child_keeps_its_progress_token`.

### H6. Every other wait has an exit

Each wait races event, deadline, cancel; first wins; ends exactly once.

1. Request to a chat-memory owner in another process: reply deadline 30 s; settled view: settle deadline + 30 s; import: 100 ms/item + 30 s (owner fsyncs each item). Miss = error shown by the turn. Own-process owner: none (actor thread is own work); run cancel ends the wait (H4.6). Failing request transform (`before_request` hook) fails the turn; never silently sends another prompt.
2. Root-turn lease: first come, first served. Stopped waiter never gets it; crashed holder's lease freed; free lease goes to the next live waiter at once. No deadline (waits for another window's turn); ends with that turn or run cancel (H4.6 drops the waiting hook); dropped wait leaves nothing.
3. Stream stall clock starts at admission slot, not before: long queue ≠ stall.

`bash.defaultTimeoutMs`: no rule; no session installs durable `bash` (`eukhe-durable/src/tools/bash.rs` has no product caller). Shell runs via the `ipython` kernel's `bash()`: cell blocks ≤ `toolBlockingBudgetMs`, then a detached job (`durable/rlm/tool.rs`); `jobs.wait` clamped to that budget.

Models: `bend/wait.bend` (event, ticks, cancel, one at a time, any order; deadline = ticks or none); `bend/lease.bend` (asks, releases, stops, crashes any order; key = arrival order). Proofs: `proof/wait/` and `proof/lease/`. Universal.

| Law | Says |
| --- | --- |
| `wait_ends_once` | Ends exactly once on event, cancel or deadline; never otherwise. |
| `wait_end_is_final` | After cancel/deadline: ended; nothing later matters. |
| `wait_arrival_wins` | Event first: ends with the event. |
| `wait_cancel_wins` | Cancel first: ends cancelled. |
| `lease_fifo` | Holder asked before every waiter; waiters in asking order (H6.2). |
| `lease_never_idle` | Held, or no live waiter: release/crash hands on at once (H6.2). |
| `lease_keeps_waiters` | Events not ending a live waiter (its release, stop, origin crash) leave it waiting or holding: none skipped (H6.2). |
| `lease_stop_never_holds` | Stopped waiter never holds (H6.2). |
| `lease_crash_frees` | Crash ends every lease of its origin, held or awaited (H6.2). |

Code: `eukhe-chord/src/context.rs` `race` (event/deadline/cancel; `Exits`, `Raced`); `memory/service.rs` `Request::reply_deadline`, `answered`, `Memory::request`, `live_parts`; `memory/service/turn.rs` `Turns` (lease), `Memory::acquire_turn` (turn-file poll `TURN_FILE_POLL`), `TurnLease::release`; `eukhe-durable/src/tasks/runtime.rs` `HookRunner::each_required` (used by `harness/generation.rs` `request` for `before_request` hooks; failure → `model_error`); `eukhe-ai/src/utils/stream_idle.rs` `StreamClock`, `ClockHold` (`ProviderRequestOptions::stream_clock`); `durable/admission_gate.rs` `AdmissionGate::admitted` (holds the clock during slot wait).

Tie: `memory::service::turn::bridge`: `race` on paused tokio (oneshot event, `advance` ticks, `AbortController`) and `Turns` (asks, releases, dropped replies, closed connections) vs `bend/bridge_wait.bend`, 304 wait + 200 lease scenarios, byte for byte. `wait_*` laws cover `race`; each wait's deadline is tied by tests: `memory::service::waits::every_request_to_a_remote_owner_but_the_lease_has_a_reply_deadline` checks `Request::reply_deadline` for every request (no catch-all: a new request must take a side). Regression: `memory::service::waits::a_stuck_owner_fails_the_request_at_its_reply_deadline`, `a_dropped_wait_for_the_turn_file_leaves_nothing_behind`; `durable::admission_gate::tests::a_queue_longer_than_the_idle_deadline_is_not_a_stall` (stalls without the clock hold); `durable::optchat::tests::a_failed_transform_fails_the_turn_and_sends_nothing`. Not modelled: owner work duration (deadline bounds the wait, not the work); turn file between owners.

### H7. A failure the harness sees is shown, with its cause

Detected failures reach the user or model with their cause.

1. Summarizer passes (compaction, branch summary) use the `auxiliaryModel` model. Unset or = session model: session model, silent. Unusable other model: session model runs it; session shows a row (selector, purpose, reason). Reasons, check order: `allowedModels` does not include it; available-models list unreadable; no model with a configured key has this name; API key not found; session model list does not include it; context window too small for the request. Row never holds auth details (may hold credentials).
2. Once per session per purpose, selector, reason; any new one = new row; reopened session shows it once again. Branch-summary row goes to the conversation shown after the move (main conversation if the summary fails or is cancelled).
3. Skill and prompt-template loaders report each failing candidate: unreadable file/entry, invalid YAML frontmatter, skill without description, unreadable ignore file, non-glob ignore rule, template path missing or not markdown, template losing a name collision. Each diagnostic: path + error text. `get_resource_snapshot` carries them in `diagnostics.skills`, `diagnostics.prompts`.
4. A tool call interrupted by crash/restart is not rerun (unless replay-safe); its result: "Tool X was interrupted and may have partially run. Check the state it changes (files, processes, jobs) before you run it again." (restart: "interrupted by a restart").

Laws (`LAWS.bend` section `progress`): `fallback_is_reported` (every substituted key noticed), `fallback_quiet_when_routed` (notice only with substitution), `fallback_quiet_when_unset`, `fallback_quiet_when_same`; `skill_failure_reported` (each candidate loaded or diagnosed), `skill_loaded_not_failed` (distinct paths: never both).

Code: `eukhe-core/src/durable/compaction/auxiliary_model.rs` (`decide_auxiliary_route`, `AuxiliaryNotices`, `show_auxiliary_notice`), `eukhe-daemon/src/branch_navigation/summary.rs`, `eukhe-core/src/skills/` (`discovery.rs`, `prompt_templates.rs`, `frontmatter.rs`), `eukhe-durable/src/harness/tool.rs` (`INTERRUPTED_NEXT_STEP`).

Tie: `decide_auxiliary_route` runs `gate` and `settle` of `bend/aux_fallback.bend` as the compiled Bend core (entry `bend/ffi_aux_fallback.bend`); `skills::bridge`: real loaders on a temp dir (good, unreadable, malformed, incomplete files) vs `bend/bridge_skill_load.bend`, 30 scenarios. Regression: `durable::compaction::tests::an_unused_auxiliary_model_shows_a_notice_once`, `skills::discovery::tests::reports_each_skill_file_and_ignore_rule_that_fails`, `skills::prompt_templates::tests::reports_each_template_that_fails`, `harness::tool::tests::recovery::answers_an_unsafe_tool_interrupted_after_intent_with_what_is_durable_only`.

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
