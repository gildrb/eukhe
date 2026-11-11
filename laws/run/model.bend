# eukhe: the laws of area run: the run, its requests, the decisions Rust
# calls and the recoveries (H4, H4.1, H4.2, H4.4, H4.7, H4.8, H4.9; the
# entry's codec, H4.10, is laws/run/entry.bend)
#
# Requirements
# ------------
# Sources: the module docs of crates/eukhe-durable/src/harness/generation/
# decide.rs, deferred.rs, note.rs and repeat.rs, the headers of
# bend/run/state.bend, bend/run/request.bend and bend/run/recovery.bend,
# and the requirement's session maintenance (the retry cap of an
# incomplete reply, the threshold of the tool-call loop guard). Rust keeps
# its counters as they grow
# (Counts: attempt, notes, ms waited, compacted; Rounds); the decisions it
# calls (decide.reply, decide.prepare, decide.compact, decide.round,
# decide.recover, decide.poll of bend/run/decision.bend, through
# bend/ffi_run.bend) take those counters. The run machine of
# bend/run/step.bend (RnStep.step, RnStep.run) and the requests of
# bend/run/request.bend (Reqs) are models: no entry runs them; the
# decisions are built from the machine's steps.
#
# H4: every run ends: after bound(cfg) inputs, whatever they are, the run
#     has ended (answered, aborted or failed); an ended run stays as it
#     ended; an abort ends a live run at once.
# H4.1: a message with a tool call is never the run's answer: its calls
#     run, whatever its text and its stop reason (vLLM, llama.cpp and
#     Ollama send the stop reason stop with tool calls); a message with
#     text and no call answers (decide.rs `Ended::reply`).
# H4.2: the round cap (maxToolRounds, at least 1): a run makes at most
#     max(cap, 1) tool rounds and the cap fails it only at that round; a
#     control (terminate, handoff) ends a round uncounted and wins over the
#     cap and a queued reset; the cap wins over a reset; else a reset ends
#     the run; else the next generation goes on with one more round and a
#     generation's whole limits (decide.rs `round_end`).
# H4.4: a deferred job is polled while the ms its request waited are below
#     the job's ms (a poll spends one ms); at that deadline the run fails
#     at the deadline; a failed poll polls the same job again only when the
#     failure is retryable and fewer than retry.maxRetries polls failed in
#     a row: the job of bend/retry.bend section 4 (deferred.rs
#     `PollFailure::next`).
# H4.7: a retry never resends a request it cut: a noted reply (a stream
#     cut as repeating, a message with no text and no call, a recovery's
#     retry) is retried with a note that names the retry's attempt and
#     spends a note of the generation (MAX_NOTES), never a retry; a
#     transient error retries the request it retries and spends a retry
#     (retry.maxRetries), never a note; an error the retry policy cannot
#     cure fails the run; the note is never logged (decide.rs `retry_note`,
#     note.rs).
# H4.8: a stuck model gets a recovery, each with a cap (decide.rs
#     `recover`; the laws are in laws/run/recover.bend): a length stop
#     with text gets length notes 1 to `long`, then the run fails (the
#     requirement's retry cap of an incomplete reply); leaked tool
#     calls the harness could not rebuild get leak notes 1 to `leak`, then
#     the run fails; calls that would make `repeat` rounds in a row with the
#     same calls and the same results do not run (the requirement's loop
#     guard threshold) and get redirect notes 1 to `redirect`,
#     then the run fails; calls below that run; a user message ends the
#     row. A recovery's retry is a noted retry (H4.7). An empty reply and a
#     length stop with no text: R4 and R7 of laws/stop.bend.
# H4.9: the decisions Rust calls make the decisions above from Rust's
#     counters: what follows a reply (H4.1, H4.4, H4.7; an overflow
#     compacts once a generation, when a cut exists, else the run fails);
#     what preparation does (spec section 8.3: a context over the blocking
#     threshold waits for its compaction, one over the background
#     threshold sends with a background compaction beside it, a generation
#     that compacted reads no threshold); whether preparation goes on after
#     the compaction it waited for (an entry goes on, a failure fails the
#     run, nothing goes on only after a threshold compaction); how a round
#     ends (H4.2). The counts left the model reads lose nothing of Rust's
#     counters, and Rust's saturation of its u64 counters changes no
#     decision.
# H4.10: the entry (bend/ffi_run.bend) answers every request Rust writes
#     with its decision, spelled; laws/run/entry.bend.

import Base
import ../../bend/ffi_run.bend as FRn
import ../../bend/retry.bend as R
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/measure.bend as RnMeasure
import ../../bend/run/request.bend as RnRequest
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../bend/wire.bend as Wr
import ../../bend/run/recovery.bend as RnRecovery

# (H4) Every run ends
# -------------------
# The model in bend/run/: one run (one user turn) through prepare, call (a
# request or a deferred poll), compact (an overflow's or a blocking
# threshold one) and tools. Every input is free: any model reply, any
# round end, any compaction result, an abort, in any order.

# LAW run_ends: every run has ended (answered, aborted or failed) after bound(cfg)
# inputs, whatever they are and whatever follows them; bound(cfg) =
# max(cap, 1)·(2 + (retries + notes + 2)·(polls + 2)), from
# compaction a generation. Notes have their own budget: a noted retry
# spends a note, never a retry
law run_ends:
  for +cfg: RnState.Cfg
  for +evs: List<&2, RnState.Ev>
  for long: {List.length(&2, RnState.Ev, evs) == RnMeasure.bound(cfg) : Nat}
  for +more: List<&2, RnState.Ev>
  {RnState.done(RnStep.run(cfg, List.append(&2, RnState.Ev, evs, more))) == True{} : Bool}

# LAW run_end_stays: an ended run stays as it ended
law run_end_stays:
  for +cfg: RnState.Cfg
  for +s: RnState.St
  for ended: {RnState.done(s) == True{} : Bool}
  for +e: RnState.Ev
  {RnStep.step(cfg, s, e) == s : RnState.St}

# LAW run_abort_ends_now: an abort ends a live run as aborted, at the next step
law run_abort_ends_now:
  for +cfg: RnState.Cfg
  for +s: RnState.St
  for live: {RnState.done(s) == False{} : Bool}
  {RnState.St.ph(RnStep.step(cfg, s, RnState.Abort{})) == RnState.Aborted{} : RnState.Ph}

# LAW run_rounds_capped: a run that has made max(cap, 1) tool rounds has failed
law run_rounds_capped:
  for +cfg: RnState.Cfg
  for +evs: List<&2, RnState.Ev>
  Or({RnState.failed(RnStep.run(cfg, evs)) == True{} : Bool}, {Nat.is_lt(RnMeasure.rounds(cfg, evs), Nat.max(RnState.Cfg.cap(cfg), 1n)) == True{} : Bool})

# The loop guard of H4.3 (run_loop_needs_repeats) is gone. The law
# `rec_never_runs_a_repeat` (H4.8) replaces it, and it is stronger: no
# row of the same calls with the same results ever gets to REPEAT_CALLS
# (5) rounds. The loop guard failed a run only after 6 such rounds.

# LAW run_rounds_fail_at_cap: the round cap fails a run only at its max(cap, 1)th round, never
# earlier
law run_rounds_fail_at_cap:
  for +cfg: RnState.Cfg
  for +evs: List<&2, RnState.Ev>
  Or({RnState.capped(RnStep.run(cfg, evs)) == False{} : Bool}, {RnMeasure.rounds(cfg, evs) == Nat.max(RnState.Cfg.cap(cfg), 1n) : Nat})

# LAW run_polls_need_defers: the poll cap fails a run only when its request's reply and each of
# its `polls` polls were deferred, polls + 1 deferred replies in a row
law run_polls_need_defers:
  for +cfg: RnState.Cfg
  for +evs: List<&2, RnState.Ev>
  Or({RnState.polled(RnStep.run(cfg, evs)) == False{} : Bool}, {RnMeasure.defers(cfg, evs) == 1n+RnState.Cfg.polls(cfg) : Nat})

# LAW run_no_answer_is_an_error: a message that ends the model's turn (any stop reason) with no
# text and no tool call never answers the run (H4.7): the model gave no
# answer, so the step is a noted error's: a retry with a note while
# notes are left, else the run fails on the model
law run_no_answer_is_an_error:
  for +cfg: RnState.Cfg
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +n: Nat
  for +p: Nat
  {RnStep.call(cfg, RnState.Ended.reply(RnState.Ended{False{}, False{}}), r, c, a, n, p) == RnStep.note(cfg, r, c, a, n, p) : RnState.St}

# LAW run_calls_never_answer: a message that ends the model's turn with a tool call never
# answers the run: its calls go to the tools phase, whatever its text and
# its stop reason. vLLM, llama.cpp and Ollama send the stop reason stop
# with tool calls
law run_calls_never_answer:
  for +cfg: RnState.Cfg
  for text: Bool
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +n: Nat
  for +p: Nat
  {RnStep.call(cfg, RnState.Ended.reply(RnState.Ended{text, True{}}), r, c, a, n, p) == RnState.St{RnState.Tools{}, r, c, a, n, p} : RnState.St}

# LAW run_note_spends_no_retry: a noted error spends a note, not a retry: retryable or not, it is
# retried with a note while notes are left, and the retries left stay
law run_note_spends_no_retry:
  for +cfg: RnState.Cfg
  for retryable: Bool
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +m: Nat
  for +p: Nat
  {RnStep.call(cfg, RnState.Error{retryable, True{}}, r, c, a, 1n+m, p) == RnState.St{RnState.Prepare{}, r, c, a, m, RnState.Cfg.polls(cfg)} : RnState.St}

# LAW run_retry_spends_no_note: a retryable error that is not noted spends a retry, not a note:
# the notes left stay
law run_retry_spends_no_note:
  for +cfg: RnState.Cfg
  for +r: Nat
  for +c: Nat
  for +b: Nat
  for +n: Nat
  for +p: Nat
  {RnStep.call(cfg, RnState.Error{True{}, False{}}, r, c, 1n+b, n, p) == RnState.St{RnState.Prepare{}, r, c, b, n, RnState.Cfg.polls(cfg)} : RnState.St}

# the input ends a round that no control stops: a round's end in the
# tools phase that goes on or resets (a control's round is not counted)
def counted_round(ph: RnState.Ph, e: RnState.Ev) -> Bool:
  match ph:
    case RnState.Tools{}:
      match e:
        case RnState.Abort{}:
          False{}
        case RnState.Go{reply, fin, got}:
          match fin:
            case RnState.Goes{}:
              True{}
            case RnState.Stops{}:
              False{}
            case RnState.Resets{}:
              True{}
    case RnState.Prepare{}:
      False{}
    case RnState.Call{}:
      False{}
    case RnState.Compact{over}:
      False{}
    case RnState.Answered{}:
      False{}
    case RnState.Aborted{}:
      False{}
    case RnState.Failed{why}:
      False{}

# r rounds left after one is spent (when spent): one fewer, never below
# none
def spend(spent: Bool, r: Nat) -> Nat:
  match spent:
    case True{}:
      match r:
        case 0n:
          0n
        case 1n+q:
          q
    case False{}:
      r

# LAW run_step_counts_rounds_down (H4.2): one input to any state of the
# model, under any configuration, spends one of the rounds left exactly
# when it ends a round that no control stops (none when none is left);
# every other input leaves the rounds left as they are
# EXCLUDES: a round counted twice or not at all, a control's round
#   counted, rounds spent by a reply, a compaction or an abort, a new
#   generation that renews the run's rounds
law run_step_counts_rounds_down:
  for +cfg: RnState.Cfg
  for +s: RnState.St
  for +e: RnState.Ev
  {RnState.St.r(RnStep.step(cfg, s, e)) == spend(counted_round(RnState.St.ph(s), e), RnState.St.r(s)) : Nat}

# (H4.7) A retry never resends a request it cut
# ---------------------------------------------
# The model of the requests in bend/run/request.bend (Reqs), stepped with
# the run machine: a model decodes the same request the same way (a greedy
# one always does), so a retry after a noted reply ends its request with
# a harness note that names the retry's attempt. A request is the version
# of its logged context and the attempt its note names. No entry runs
# this model: Rust builds its notes itself (decide.rs `retry_note`), so the
# laws of this section are about the model. What Rust runs of it is the
# decision after a noted reply (run_note_budget, run_message_reply).

# LAW run_retry_sends_a_new_request (H4.7): in the model of the requests,
# after any inputs under any configuration, the log never shows a request
# sent after a request equal to it was cut (`fresh` of
# bend/run/request.bend): a retry after a cut sends neither the request it
# cut nor any other one the run cut, cut after cut until the notes run out
law run_retry_sends_a_new_request:
  for +cfg: RnState.Cfg
  for +evs: List<&2, RnState.Ev>
  {RnRequest.fresh(RnRequest.Reqs.log(RnRequest.reqs(cfg, evs))) == True{} : Bool}

# LAW run_cut_names_the_request (H4.7): in the model of the requests, a
# noted error to the request out (the call phase) logs a cut of the
# request its context and note name, and the next request is at attempt
# n + 1 with the note of attempt n + 1, whatever phase follows
law run_cut_names_the_request:
  for -retryable: Bool
  for -fin: RnState.Fin
  for -got: RnState.Got
  for -pa: RnState.Ph
  for -ctx: Nat
  for -n: Nat
  for -note: Nat
  for -log: List<&2, RnRequest.Sent>
  {RnRequest.Reqs.step(RnState.Call{}, RnState.Go{RnState.Error{retryable, True{}}, fin, got}, pa, RnRequest.Reqs{ctx, n, note, log}) == RnRequest.Reqs{ctx, 1n+n, 1n+n, RnRequest.Cut{RnRequest.Req{ctx, note}} <> log} : RnRequest.Reqs}

# LAW run_note_is_never_logged (H4.7): in the model of the requests, the
# lines the model says the run logs of a request (`logged` of its
# `Req.lines`) are those of its context with no note: the note changes
# what the model reads, never what the model logs (the log of
# generation.rs is not modelled here)
law run_note_is_never_logged:
  for q: RnRequest.Req
  {RnRequest.logged(RnRequest.Req.lines(q)) == RnRequest.logged(RnRequest.Req.lines(RnRequest.Req{RnRequest.Req.ctx(q), 0n})) : List<&2, RnRequest.Line>}

# the requests a and b name the same context and the same note
def same_req(a: RnRequest.Req, b: RnRequest.Req) -> Bool:
  match a b:
    case RnRequest.Req{c, m} RnRequest.Req{d, k}:
      Bool.and(Nat.is_eq(c, d), Nat.is_eq(m, k))

# the newest request sent in xs (newest first) is q
def sent_last_is(+q: RnRequest.Req, xs: List<&2, RnRequest.Sent>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case RnRequest.Sent{p} <> t:
      same_req(p, q)
    case RnRequest.Cut{p} <> t:
      sent_last_is(q, t)

# every cut of xs (newest first) names the newest request sent before it
def cuts_name_sends(xs: List<&2, RnRequest.Sent>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case RnRequest.Sent{q} <> t:
      cuts_name_sends(t)
    case RnRequest.Cut{+q} <> +t:
      Bool.and(sent_last_is(q, t), cuts_name_sends(t))

# LAW run_cut_names_the_last_sent (H4.7): in the model of the requests,
# after any inputs under any configuration, every cut in the log names
# the request sent last before it: a noted reply cuts the request it
# answers, never another one, and never with no request sent
# EXCLUDES: a cut that names an older request, a request of another
#   context or with another note, a cut logged before any request
law run_cut_names_the_last_sent:
  for +cfg: RnState.Cfg
  for evs: List<&2, RnState.Ev>
  {cuts_name_sends(RnRequest.Reqs.log(RnRequest.reqs(cfg, evs))) == True{} : Bool}

# the requests sent in xs
def sents(xs: List<&2, RnRequest.Sent>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case RnRequest.Sent{q} <> t:
      1n+sents(t)
    case RnRequest.Cut{q} <> t:
      sents(t)

# a step from phase pb to phase pa sends a request: preparation that ends
# in a call
def sends_one(pb: RnState.Ph, pa: RnState.Ph) -> Nat:
  match pb:
    case RnState.Prepare{}:
      match pa:
        case RnState.Call{}:
          1n
        case RnState.Prepare{}:
          0n
        case RnState.Compact{over}:
          0n
        case RnState.Tools{}:
          0n
        case RnState.Answered{}:
          0n
        case RnState.Aborted{}:
          0n
        case RnState.Failed{why}:
          0n
    case RnState.Call{}:
      0n
    case RnState.Compact{over}:
      0n
    case RnState.Tools{}:
      0n
    case RnState.Answered{}:
      0n
    case RnState.Aborted{}:
      0n
    case RnState.Failed{why}:
      0n

# the requests the run sends on the inputs evs from the state s
def calls_made(evs: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +s: RnState.St) -> Nat:
  match evs:
    case Nil{}:
      0n
    case +e <> rest:
      +s2 = RnStep.step(cfg, s, e)
      Nat.add(calls_made(rest, cfg, s2), sends_one(RnState.St.ph(s), RnState.St.ph(s2)))

# LAW run_every_call_is_logged (H4.7): in the model of the requests, after
# any inputs under any configuration, the log holds one sent request for
# each step of the run machine that took the run from preparation into a
# call
# EXCLUDES: requests that log nothing (an empty log passes
#   run_retry_sends_a_new_request), a request sent and not logged, a
#   request logged twice or logged by a step that sends none
law run_every_call_is_logged:
  for +cfg: RnState.Cfg
  for +evs: List<&2, RnState.Ev>
  {sents(RnRequest.Reqs.log(RnRequest.reqs(cfg, evs))) == calls_made(evs, cfg, RnState.init(cfg)) : Nat}

# (H4.9) The decisions Rust calls
# -------------------------------
# The decisions of bend/run/decision.bend that decide.rs and deferred.rs
# call through the compiled core (bend/ffi_run.bend; laws/run/entry.bend
# pins the codec). Each takes Rust's counters as they grow: the limits
# (Lim: maxToolRounds, the job's ms, retry.maxRetries, MAX_NOTES) and the
# counts of a request (At: its attempt, 1 for a generation's first
# request and one more per retry; the noted retries so far; the ms it
# waited; whether the generation compacted). A generation's request after
# i transient retries and j noted retries is at attempt 1 + i + j with j
# notes (decide.rs `retry_note`: every retry adds an attempt, a noted one
# a note too).

# x when b, else y
def then_if(b: Bool, x: RnDecision.Then, y: RnDecision.Then) -> RnDecision.Then:
  match b:
    case True{}:
      x
    case False{}:
      y

# LAW run_reply_answers_or_runs_tools (H4.1): under any limits, from any
# counts, a reply with text and no call answers the run and a reply with
# tool calls runs its tools
# EXCLUDES: calls taken as the answer, an answer retried or failed
law run_reply_answers_or_runs_tools:
  for +l: RnDecision.Lim
  for +t: RnDecision.At
  {RnDecision.decide.reply(l, t, RnState.Plain{}) == RnDecision.DoAnswer{} : RnDecision.Then} &
  {RnDecision.decide.reply(l, t, RnState.Calls{}) == RnDecision.DoTools{} : RnDecision.Then}

# LAW run_retry_budget (H4.7): under any limits, a transient error the
# retry policy can cure, to the request after i transient retries and j
# noted retries of its generation (attempt 1 + i + j, j notes; any ms
# waited, compacted or not), is retried exactly while i is below
# retry.maxRetries, else the run fails: the noted retries spend none of
# the retries
# EXCLUDES: a retry past retry.maxRetries, one retry too few, notes
#   counted against the retries, a retry read as a noted retry
law run_retry_budget:
  for +l: RnDecision.Lim
  for +i: Nat
  for +j: Nat
  for +w: Nat
  for +c: Bool
  {RnDecision.decide.reply(l, RnDecision.At{1n+Nat.add(j, i), j, w, c}, RnState.Error{True{}, False{}}) == then_if(Nat.is_lt(i, RnDecision.Lim.retries(l)), RnDecision.DoRetry{}, RnDecision.DoFail{}) : RnDecision.Then}

# LAW run_unretryable_error_fails (H4.7): under any limits, from any
# counts, an error that is not noted and that the retry policy cannot
# cure fails the run on the model
# EXCLUDES: a retry of an error the policy cannot cure
law run_unretryable_error_fails:
  for +l: RnDecision.Lim
  for +t: RnDecision.At
  {RnDecision.decide.reply(l, t, RnState.Error{False{}, False{}}) == RnDecision.DoFail{} : RnDecision.Then}

# LAW run_note_budget (H4.7): under any limits, from any counts, a noted
# reply (retryable or not) is retried with a note exactly while the
# generation's noted retries are below MAX_NOTES (the limits' notes),
# else the run fails; the transient retries spend none of the notes
# EXCLUDES: a noted reply retried as a transient error (the request it
#   cut sent again), a note past MAX_NOTES, one note too few, retries
#   counted against the notes
law run_note_budget:
  for +l: RnDecision.Lim
  for +t: RnDecision.At
  for +retryable: Bool
  {RnDecision.decide.reply(l, t, RnState.Error{retryable, True{}}) == then_if(Nat.is_lt(RnDecision.At.notes(t), RnDecision.Lim.notes(l)), RnDecision.DoNote{}, RnDecision.DoFail{}) : RnDecision.Then}

# LAW run_deferred_polls_until_deadline (H4.4): under any limits, from any
# counts, a deferred reply polls the same job while the ms its request
# waited are below the job's ms, else the run fails at the job's deadline
# (not on the model)
# EXCLUDES: a poll past the deadline, a deadline one poll early, the
#   deadline read as a failure on the model
law run_deferred_polls_until_deadline:
  for +l: RnDecision.Lim
  for +t: RnDecision.At
  {RnDecision.decide.reply(l, t, RnState.Deferred{}) == then_if(Nat.is_lt(RnDecision.At.waited(t), RnDecision.Lim.wait(l)), RnDecision.DoPoll{}, RnDecision.DoLate{}) : RnDecision.Then}

# LAW run_overflow_compacts_once (H4.9): under any limits, at any attempt,
# notes and ms waited, an overflow with a cut compacts when the generation
# has not compacted and fails the run when it has; an overflow with no cut
# fails the run from any counts
# EXCLUDES: a second compaction in a generation, a compaction with no
#   cut, an overflow retried
law run_overflow_compacts_once:
  for +l: RnDecision.Lim
  for +a: Nat
  for +j: Nat
  for +w: Nat
  for +t: RnDecision.At
  {RnDecision.decide.reply(l, RnDecision.At{a, j, w, False{}}, RnState.Overflow{True{}}) == RnDecision.DoCompact{} : RnDecision.Then} &
  {RnDecision.decide.reply(l, RnDecision.At{a, j, w, True{}}, RnState.Overflow{True{}}) == RnDecision.DoFail{} : RnDecision.Then} &
  {RnDecision.decide.reply(l, t, RnState.Overflow{False{}}) == RnDecision.DoFail{} : RnDecision.Then}

# LAW run_message_reply (H4.1, H4.7): what follows a message that ends the
# model's turn, read by Ended.reply and then decided by decide.reply (the
# two calls Rust makes), under any limits and from any counts: a message
# with a tool call runs its tools whatever its text; one with text and no
# call answers; one with neither gave no answer and is a noted reply,
# retried with a note while the notes last, else the run fails
# EXCLUDES: calls with text answered, an empty message answered or
#   retried as a transient error (the same request sent again)
law run_message_reply:
  for text: Bool
  for +l: RnDecision.Lim
  for +t: RnDecision.At
  {RnDecision.decide.reply(l, t, RnState.Ended.reply(RnState.Ended{text, True{}})) == RnDecision.DoTools{} : RnDecision.Then} &
  {RnDecision.decide.reply(l, t, RnState.Ended.reply(RnState.Ended{True{}, False{}})) == RnDecision.DoAnswer{} : RnDecision.Then} &
  {RnDecision.decide.reply(l, t, RnState.Ended.reply(RnState.Ended{False{}, False{}})) == then_if(Nat.is_lt(RnDecision.At.notes(t), RnDecision.Lim.notes(l)), RnDecision.DoNote{}, RnDecision.DoFail{}) : RnDecision.Then}

# LAW run_prepare_follows_the_thresholds (H4.9, spec section 8.3): a
# context under every threshold sends its request with no compaction,
# compacted or not; a generation that compacted sends with no compaction
# whatever its context is over (it compacts at most once); one that has
# not compacted sends with a background compaction beside the request
# over the background threshold and waits for the compaction over the
# blocking one
# EXCLUDES: a blocking compaction after the generation compacted (a
#   compaction loop), a request sent over the blocking threshold, a
#   background compaction under it or never started
law run_prepare_follows_the_thresholds:
  for +compacted: Bool
  for +th: RnDecision.Th
  {RnDecision.decide.prepare(compacted, RnDecision.Under{}) == RnDecision.Sends{False{}} : RnDecision.Prepared} &
  {RnDecision.decide.prepare(True{}, th) == RnDecision.Sends{False{}} : RnDecision.Prepared} &
  {RnDecision.decide.prepare(False{}, RnDecision.Background{}) == RnDecision.Sends{True{}} : RnDecision.Prepared} &
  {RnDecision.decide.prepare(False{}, RnDecision.Blocking{}) == RnDecision.Waits{} : RnDecision.Prepared}

# LAW run_compact_goes_on_with_room (H4.9): after the compaction preparation
# waited for, an overflow's or a blocking threshold one: one that appended
# its entry goes on; one that failed fails the run; one that found nothing
# goes on exactly when it was a threshold one (the request may still fit;
# an overflow's request overflows again)
# EXCLUDES: preparation that goes on after a failed compaction or after
#   an overflow's that found nothing, a threshold compaction that found
#   nothing failing the run, an entry that fails it
law run_compact_goes_on_with_room:
  for +over: Bool
  {RnDecision.decide.compact(over, RnState.Built{}) == True{} : Bool} &
  {RnDecision.decide.compact(over, RnState.Broke{}) == False{} : Bool} &
  {RnDecision.decide.compact(over, RnState.Kept{}) == Bool.not(over) : Bool}

# LAW run_round_control_stops (H4.2): under any limits, after any rounds,
# a round a control ends (terminate, handoff) stops the run, whether or
# not a reset is queued and whatever the cap
# EXCLUDES: a control that loses to a reset or to the cap, a control's
#   round handed on
law run_round_control_stops:
  for +l: RnDecision.Lim
  for +count: Nat
  for +reset: Bool
  {RnDecision.decide.round(l, count, True{}, reset) == RnDecision.EndStop{} : RnDecision.End}

# LAW run_round_capped_at_max (H4.2): under any limits, a round no control
# ends that makes the run's maxToolRounds-th round or a later one (count +
# 1 rounds made, at least the limits' rounds) caps the run, whether or not
# a reset is queued
# EXCLUDES: a round past the cap handed on, a reset that wins over the
#   cap
law run_round_capped_at_max:
  for +l: RnDecision.Lim
  for +count: Nat
  for +reset: Bool
  for at: {Nat.is_le(RnDecision.Lim.rounds(l), 1n+count) == True{} : Bool}
  {RnDecision.decide.round(l, count, False{}, reset) == RnDecision.EndCapped{} : RnDecision.End}

# LAW run_round_goes_on_below_max (H4.2): under any limits, a round no
# control ends that makes fewer than maxToolRounds rounds (count + 1 below
# the limits' rounds) hands the run on with count + 1 rounds made, or,
# with a reset queued, ends it with the reset
# EXCLUDES: a cap one round early, a round handed on without counting
#   itself or counting two, a queued reset ignored
law run_round_goes_on_below_max:
  for +l: RnDecision.Lim
  for +count: Nat
  for +below: {Nat.is_lt(1n+count, RnDecision.Lim.rounds(l)) == True{} : Bool}
  {RnDecision.decide.round(l, count, False{}, False{}) == RnDecision.EndNext{1n+count} : RnDecision.End} &
  {RnDecision.decide.round(l, count, False{}, True{}) == RnDecision.EndReset{} : RnDecision.End}

# LAW run_prepare_compacted_reads_no_threshold: a generation that compacted reads no threshold: whatever its
# context is over, it prepares as if under every threshold. So Rust need
# not measure the context (a provider's count is a request) after the
# generation compacted
law run_prepare_compacted_reads_no_threshold:
  for +th: RnDecision.Th
  {RnDecision.decide.prepare(True{}, th) == RnDecision.decide.prepare(True{}, RnDecision.Under{}) : RnDecision.Prepared}

# LAW run_round_counts_down: a round that no control stops leaves the rounds left of the run of
# count + 1 rounds: the model counts down as Rust counts up
law run_round_counts_down:
  for +l: RnDecision.Lim
  for +count: Nat
  for +reset: Bool
  for +c: Nat
  for +a: Nat
  for +n: Nat
  for +p: Nat
  {RnState.St.r(RnStep.tools(RnDecision.Lim.cfg(l), RnDecision.fin.of(False{}, reset), RnDecision.Lim.r(l, count), c, a, n, p)) == RnDecision.Lim.r(l, 1n+count) : Nat}

# the counts of the request a noted retry sends: one more attempt and
# one more note (`retry_note`, then the retry phase)
def rust.noted_next(t: RnDecision.At) -> RnDecision.At:
  match t:
    case RnDecision.At{attempt, notes, waited, compacted}:
      RnDecision.At{1n+attempt, 1n+notes, 0n, compacted}

# the counts of the request a transient retry sends: one more attempt
def rust.retried_next(t: RnDecision.At) -> RnDecision.At:
  match t:
    case RnDecision.At{attempt, notes, waited, compacted}:
      RnDecision.At{1n+attempt, notes, 0n, compacted}

# LAW run_note_counts_down: a noted reply leaves the notes left of the request its retry
# sends
law run_note_counts_down:
  for +l: RnDecision.Lim
  for +t: RnDecision.At
  for +r: Nat
  for +c: Nat
  for +p: Nat
  {RnState.St.n(RnStep.note(RnDecision.Lim.cfg(l), r, c, RnDecision.At.a(l, t), RnDecision.At.n(l, t), p)) == RnDecision.At.n(l, rust.noted_next(t)) : Nat}

# LAW run_note_keeps_the_retries: a noted reply leaves the retries left of the request its retry
# sends: a note spends no retry
law run_note_keeps_the_retries:
  for +l: RnDecision.Lim
  for +t: RnDecision.At
  for +r: Nat
  for +c: Nat
  for +p: Nat
  {RnState.St.a(RnStep.note(RnDecision.Lim.cfg(l), r, c, RnDecision.At.a(l, t), RnDecision.At.n(l, t), p)) == RnDecision.At.a(l, rust.noted_next(t)) : Nat}

# LAW run_retry_counts_down: a retryable error leaves the retries left of the request its retry
# sends, for every request whose attempts count its notes (attempt >=
# 1 + notes, as every request of a generation has)
law run_retry_counts_down:
  for +l: RnDecision.Lim
  for +t: RnDecision.At
  for +e: {Nat.is_le(1n+RnDecision.At.notes(t), RnDecision.At.attempt(t)) == True{} : Bool}
  for +r: Nat
  for +c: Nat
  for +p: Nat
  {RnState.St.a(RnStep.retry(RnDecision.Lim.cfg(l), True{}, r, c, RnDecision.At.a(l, t), RnDecision.At.n(l, t), p)) == RnDecision.At.a(l, rust.retried_next(t)) : Nat}

# LAW run_retry_premise_witness: witness: a request whose attempts count its notes exists
law run_retry_premise_witness:
  exs t: RnDecision.At
  {Nat.is_le(1n+RnDecision.At.notes(t), RnDecision.At.attempt(t)) == True{} : Bool}

# LAW run_retry_keeps_the_notes: a retryable error leaves the notes left of the request its retry
# sends: a retry spends no note
law run_retry_keeps_the_notes:
  for +l: RnDecision.Lim
  for +t: RnDecision.At
  for +r: Nat
  for +c: Nat
  for +p: Nat
  {RnState.St.n(RnStep.retry(RnDecision.Lim.cfg(l), True{}, r, c, RnDecision.At.a(l, t), RnDecision.At.n(l, t), p)) == RnDecision.At.n(l, rust.retried_next(t)) : Nat}

# the counts of a request within its limits: notes at most MAX_NOTES,
# an attempt per note and one more, retries spent at most
# retry.maxRetries, the ms waited at most the job's
def rust.within(l: RnDecision.Lim, t: RnDecision.At) -> Bool:
  match l:
    case RnDecision.Lim{rounds, wait, retries, most}:
      match t:
        case RnDecision.At{+attempt, +notes, waited, compacted}:
          Bool.and(Nat.is_le(notes, most), Bool.and(Nat.is_le(1n+notes, attempt), Bool.and(Nat.is_le(Nat.sub(Nat.sub(attempt, 1n), notes), retries), Nat.is_le(waited, wait))))

# the counts Rust keeps, read back from the counts left
def rust.back(l: RnDecision.Lim, a: Nat, +n: Nat, p: Nat, c: Nat) -> RnDecision.At:
  match l:
    case RnDecision.Lim{rounds, wait, retries, +most}:
      RnDecision.At{1n+Nat.add(Nat.sub(retries, a), Nat.sub(most, n)), Nat.sub(most, n), Nat.sub(wait, p), Nat.is_eq(c, 0n)}

# LAW run_counts_lossless: the counts left lose nothing: within its limits, a request's
# counts come back from the counts left the model reads
law run_counts_lossless:
  for +l: RnDecision.Lim
  for +t: RnDecision.At
  for +w: {rust.within(l, t) == True{} : Bool}
  {rust.back(l, RnDecision.At.a(l, t), RnDecision.At.n(l, t), RnDecision.At.p(l, t), RnDecision.At.c(t)) == t : RnDecision.At}

# LAW run_counts_within_witness: witness: counts within their limits exist
law run_counts_within_witness:
  exs l: RnDecision.Lim
  exs t: RnDecision.At
  {rust.within(l, t) == True{} : Bool}

# LAW run_rounds_lossless: the rounds left lose nothing: below the cap, the rounds made come
# back from the rounds left
law run_rounds_lossless:
  for +l: RnDecision.Lim
  for +count: Nat
  for +w: {Nat.is_lt(count, RnDecision.Lim.rounds(l)) == True{} : Bool}
  {Nat.sub(Nat.sub(RnDecision.Lim.rounds(l), 1n), RnDecision.Lim.r(l, count)) == count : Nat}

# LAW run_rounds_within_witness: witness: a run below its round cap exists
law run_rounds_within_witness:
  exs l: RnDecision.Lim
  exs count: Nat
  {Nat.is_lt(count, RnDecision.Lim.rounds(l)) == True{} : Bool}

# what a failed poll of a live job does in Rust: poll again when
# `PollFailure::next` repolls and the poll's time check (a deferred reply)
# polls; else cancel the job
def rust.job(repoll: Bool, t: RnDecision.Then) -> R.Act:
  match repoll:
    case True{}:
      match t:
        case RnDecision.DoPoll{}:
          R.Poll{}
        case RnDecision.DoAnswer{}:
          R.Cancel{}
        case RnDecision.DoTools{}:
          R.Cancel{}
        case RnDecision.DoRetry{}:
          R.Cancel{}
        case RnDecision.DoNote{}:
          R.Cancel{}
        case RnDecision.DoCompact{}:
          R.Cancel{}
        case RnDecision.DoFail{}:
          R.Cancel{}
        case RnDecision.DoLate{}:
          R.Cancel{}
    case False{}:
      R.Cancel{}

# what a deferred reply does to the job in Rust: poll again, or cancel it
# at its deadline
def rust.later(t: RnDecision.Then) -> R.Act:
  match t:
    case RnDecision.DoPoll{}:
      R.Poll{}
    case RnDecision.DoAnswer{}:
      R.Cancel{}
    case RnDecision.DoTools{}:
      R.Cancel{}
    case RnDecision.DoRetry{}:
      R.Cancel{}
    case RnDecision.DoNote{}:
      R.Cancel{}
    case RnDecision.DoCompact{}:
      R.Cancel{}
    case RnDecision.DoFail{}:
      R.Cancel{}
    case RnDecision.DoLate{}:
      R.Cancel{}

# LAW run_failed_poll_is_the_job_model: a failed poll of a live job, from any counts, does what the job of
# bend/retry.bend section 4 does with the ms left (wait - waited): it
# polls the same job again exactly when that job does
law run_failed_poll_is_the_job_model:
  for +l: RnDecision.Lim
  for +t: RnDecision.At
  for +retryable: Bool
  for +failed: Nat
  for +budget: Nat
  for +gap: Nat
  {rust.job(RnDecision.decide.poll(retryable, failed, RnDecision.Lim.retries(l)), RnDecision.decide.reply(l, t, RnState.Deferred{})) == R.Step.act(R.step(RnDecision.Lim.retries(l), budget, R.Live{failed, RnDecision.At.p(l, t)}, R.Broke{retryable, gap})) : R.Act}

# LAW run_deferred_reply_is_the_job_model: a deferred reply to a poll of a live job, from any counts, does
# what the job of bend/retry.bend section 4 does with the ms left: it
# polls again exactly when that job does, else the job is cancelled at
# its deadline
law run_deferred_reply_is_the_job_model:
  for +l: RnDecision.Lim
  for +t: RnDecision.At
  for +fails: Nat
  for +budget: Nat
  for +failed: Nat
  for +gap: Nat
  {rust.later(RnDecision.decide.reply(l, t, RnState.Deferred{})) == R.Step.act(R.step(fails, budget, R.Live{failed, RnDecision.At.p(l, t)}, R.Later{gap})) : R.Act}

# LAW run_first_deferred_reply_is_the_job_model: the first deferred reply of a request does what the job of
# bend/retry.bend section 4 does with a new job of the ms left
law run_first_deferred_reply_is_the_job_model:
  for +l: RnDecision.Lim
  for +t: RnDecision.At
  for +fails: Nat
  for +gap: Nat
  {rust.later(RnDecision.decide.reply(l, t, RnState.Deferred{})) == R.Step.act(R.step(fails, RnDecision.At.p(l, t), R.NoJob{}, R.Later{gap})) : R.Act}

# the limits with the job's ms saturated at cap
def rust.sat_wait(l: RnDecision.Lim, +cap: Nat) -> RnDecision.Lim:
  match l:
    case RnDecision.Lim{rounds, wait, retries, most}:
      RnDecision.Lim{rounds, Nat.min(wait, cap), retries, most}

# the counts with the attempt saturated at cap
def rust.sat_attempt(t: RnDecision.At, +cap: Nat) -> RnDecision.At:
  match t:
    case RnDecision.At{attempt, notes, waited, compacted}:
      RnDecision.At{Nat.min(attempt, cap), notes, waited, compacted}

# LAW run_reply_saturates_the_wait: Rust saturates the job's ms and the ms waited (u64s) at the wire's
# largest Nat (10^14 - 1) before it encodes them: for a request that
# waited less than any cap (10^14 ms is 3000 years), the step after any
# reply is the same. A wait at the cap never ends a job that waited less
law run_reply_saturates_the_wait:
  for +l: RnDecision.Lim
  for +t: RnDecision.At
  for +reply: RnState.Reply
  for +cap: Nat
  for +e: {Nat.is_lt(RnDecision.At.waited(t), cap) == True{} : Bool}
  {RnDecision.decide.reply(rust.sat_wait(l, cap), t, reply) == RnDecision.decide.reply(l, t, reply) : RnDecision.Then}

# LAW run_reply_saturates_the_attempt: Rust saturates the attempt (a u64) at the wire's largest Nat: any
# cap above notes + retry.maxRetries (two u32s) leaves the step after any
# reply the same (an attempt at the cap has spent every retry, as a
# larger one)
law run_reply_saturates_the_attempt:
  for +l: RnDecision.Lim
  for +t: RnDecision.At
  for +reply: RnState.Reply
  for +cap: Nat
  for +e: {Nat.is_lt(Nat.add(RnDecision.At.notes(t), RnDecision.Lim.retries(l)), cap) == True{} : Bool}
  {RnDecision.decide.reply(l, rust.sat_attempt(t, cap), reply) == RnDecision.decide.reply(l, t, reply) : RnDecision.Then}

# LAW run_entry_example (H4.10): anchor (no coverage): the wire strings Rust writes and
# the answers it reads, one of each request: the third empty note in a
# row (row 3, the cap) quits, the second one (row 2) redoes with note 3;
# a deferred reply that waited less than its job polls; a message with
# no text and no call is a noted error; a blocking threshold waits; a
# threshold compaction that found nothing goes on; a round below the cap
# goes on with one more round; a failed retryable poll below the cap
# polls again; input left over; an unknown tag
# EXCLUDES: a field order other than Rust's, another answer spelling, an
#   empty reply redone past its cap
law run_entry_example:
  {[FRn.ffi("5,3,2,2,5,3,4,3,"), FRn.ffi("5,3,2,2,5,3,4,2,"), FRn.ffi("0,250,600000,3,4,1,0,10,F2,"), FRn.ffi("1,FF"), FRn.ffi("2,F2,"), FRn.ffi("3,F1,"), FRn.ffi("4,250,600000,3,4,7,FF"), FRn.ffi("6,T2,3,"), FRn.ffi("5,3,2,2,5,3,4,3,x"), FRn.ffi("7,")] == ["2,", "1,3,", "2,", "3,FT", "0,", "T", "3,8,", "T", Wr.err("run: input left over after the request"), Wr.err("run: malformed request")] : List<&2, String>}

# LAW rec_calls_run: tool calls that make fewer than `repeat` rounds in a row run: the
# recoveries never stop a call that is not a repeat. The rounds in a row
# grow when the results are those of the last round; when the results
# change (a poll of a job that makes progress), a new row of 1 starts
law rec_calls_run:
  for +rc: RnRecovery.RCfg
  for +h: Nat
  for +kept: Bool
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for fresh: {RnRecovery.below(RnRecovery.again(same, last, h), RnRecovery.RCfg.repeat(rc)) == True{} : Bool}
  {RnRecovery.Rec.step(rc, RnRecovery.Ran{h, kept}, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Exec{}, RnRecovery.Rec{RnRecovery.Free{}, 0n, RnRecovery.ran.same(kept, RnRecovery.again(same, last, h)), h}} : RnRecovery.Dec}

# LAW rec_repeat_redirects: such a repeat, under the cap, is retried with the next redirect
# note
law rec_repeat_redirects:
  for +rc: RnRecovery.RCfg
  for +h: Nat
  for kept: Bool
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for rep: {RnRecovery.below(RnRecovery.again(same, last, h), RnRecovery.RCfg.repeat(rc)) == False{} : Bool}
  for under: {RnRecovery.below(RnRecovery.Rk.loops(k, row), RnRecovery.RCfg.redirect(rc)) == True{} : Bool}
  {RnRecovery.Rec.step(rc, RnRecovery.Ran{h, kept}, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Loops{}, 1n+RnRecovery.Rk.loops(k, row), same, last}} : RnRecovery.Dec}

# LAW rec_redo_is_noted: a recovery's retry is a noted error, so its request ends with the
# note of the next attempt (run_cut_names_the_request): it never sends
# the request again (run_retry_sends_a_new_request)
law rec_redo_is_noted:
  for -pass: RnState.Reply
  {RnRecovery.Act.reply(RnRecovery.Redo{}, pass) == RnState.Error{False{}, True{}} : RnState.Reply}
