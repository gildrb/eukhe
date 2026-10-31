# eukhe: the laws of area run

import Base
import ../bend/ffi_run.bend as FRn
import ../bend/retry.bend as R
import ../bend/run/decision.bend as RnDecision
import ../bend/run/measure.bend as RnMeasure
import ../bend/run/recovery.bend as RnRecovery
import ../bend/run/request.bend as RnRequest
import ../bend/run/state.bend as RnState
import ../bend/run/step.bend as RnStep
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (H4) Every run ends
# -------------------
# LAWS.bend H4, the model in bend/run/: one run (one user turn)
# through prepare, call (a request or a deferred poll), compact (an
# overflow's or a blocking threshold one) and tools. Every input is free:
# any model reply, any round end, any compaction result, an abort, in any
# order.

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

# (H4.7) A retry never resends a request it cut
# ---------------------------------------------
# LAWS.bend H4.7, the requests of bend/run/request.bend: a model decodes
# the same request the same way (a greedy one always does), so a retry
# after a noted reply (the stream repeated itself until the guard cut it,
# or the reply gave no answer) ends its request with a harness note that
# names the retry's attempt. A request is the version of its logged
# context and the attempt its note names.

# LAW run_retry_sends_a_new_request: no request the run sends is equal to a request it sent before and
# had cut: a retry after a cut sends neither the request it cut nor any
# other one the run cut, whatever the inputs, cut after cut until the
# notes run out
law run_retry_sends_a_new_request:
  for +cfg: RnState.Cfg
  for +evs: List<&2, RnState.Ev>
  {RnRequest.fresh(RnRequest.Reqs.log(RnRequest.reqs(cfg, evs))) == True{} : Bool}

# LAW run_cut_names_the_request: a noted reply cuts the request the run sent, and the next request
# carries the note of the next attempt
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

# LAW run_note_is_never_logged: the note changes what the model reads, never what the run logs:
# a request logs the same lines as its context with no note
law run_note_is_never_logged:
  for q: RnRequest.Req
  {RnRequest.logged(RnRequest.Req.lines(q)) == RnRequest.logged(RnRequest.Req.lines(RnRequest.Req{RnRequest.Req.ctx(q), 0n})) : List<&2, RnRequest.Line>}

# (H4.9) The decisions Rust calls are the model's
# -----------------------------------------------
# LAWS.bend H4, the decisions of bend/run/decision.bend that
# crates/eukhe-durable/src/harness/generation/decide.rs and deferred.rs
# call through the compiled core (decide.reply, decide.prepare,
# decide.compact, decide.round, decide.poll; decide.recover in section
# recover). Rust keeps its counters as they grow (Counts, Rounds); each
# decision makes the counts left of the model from them, takes the
# model's step and reads its answer back. The helpers rust.* are the
# rules as decide.rs and deferred.rs wrote them before the core took
# them over, over the counts that grow. The laws prove every decision
# equal to its rule for every input (the projection is exact), the
# counts left lose nothing of the counts Rust keeps, they count down
# exactly as Rust's counts grow, a failed poll and a deferred reply do
# what the deferred job of bend/retry.bend section 4 does, and the cap
# Rust saturates its 64-bit counts at (the wire's largest Nat, below the
# core's Nat range) changes no decision.

# the step after a deferred reply, as `after_reply` took it: poll the
# same job while the request waited less than the job may run
def rust.wait(waits: Bool) -> RnDecision.Then:
  match waits:
    case True{}:
      RnDecision.DoPoll{}
    case False{}:
      RnDecision.DoLate{}

# a noted reply retries with a note while notes are left
def rust.noted(left: Bool) -> RnDecision.Then:
  match left:
    case True{}:
      RnDecision.DoNote{}
    case False{}:
      RnDecision.DoFail{}

# an error that is not noted retries while it is retryable and retries
# are left
def rust.retry(left: Bool) -> RnDecision.Then:
  match left:
    case True{}:
      RnDecision.DoRetry{}
    case False{}:
      RnDecision.DoFail{}

# an overflow compacts when a cut exists and the generation has not
# compacted
def rust.over(compacts: Bool) -> RnDecision.Then:
  match compacts:
    case True{}:
      RnDecision.DoCompact{}
    case False{}:
      RnDecision.DoFail{}

# `after_reply`: the retries spent are the attempts after the first that
# were not noted, (attempt - 1) - notes
def rust.after_reply(l: RnDecision.Lim, t: RnDecision.At, reply: RnState.Reply) -> RnDecision.Then:
  match l:
    case RnDecision.Lim{rounds, wait, retries, most}:
      match t:
        case RnDecision.At{attempt, +notes, waited, compacted}:
          match reply:
            case RnState.Plain{}:
              RnDecision.DoAnswer{}
            case RnState.Calls{}:
              RnDecision.DoTools{}
            case RnState.Deferred{}:
              rust.wait(Nat.is_lt(waited, wait))
            case RnState.Error{retryable, noted}:
              match noted:
                case True{}:
                  rust.noted(Nat.is_lt(notes, most))
                case False{}:
                  rust.retry(Bool.and(retryable, Nat.is_lt(Nat.sub(Nat.sub(attempt, 1n), notes), retries)))
            case RnState.Overflow{cut}:
              rust.over(Bool.and(cut, Bool.not(compacted)))

# LAW run_reply_is_the_rust_rule: the step after any reply, from any counts and limits, is the one
# `after_reply` took: the counts left that the model reads (At.a, At.n,
# At.p, At.c) are exact
law run_reply_is_the_rust_rule:
  for +l: RnDecision.Lim
  for +t: RnDecision.At
  for +reply: RnState.Reply
  {RnDecision.decide.reply(l, t, reply) == rust.after_reply(l, t, reply) : RnDecision.Then}

# `before_request`: a generation that compacted sends its request with no
# compaction; else a context over the blocking threshold (with a cut)
# waits for a compaction, and one over the background threshold sends
# with a background compaction beside it
def rust.before_request(compacted: Bool, th: RnDecision.Th) -> RnDecision.Prepared:
  match compacted:
    case True{}:
      RnDecision.Sends{False{}}
    case False{}:
      match th:
        case RnDecision.Under{}:
          RnDecision.Sends{False{}}
        case RnDecision.Background{}:
          RnDecision.Sends{True{}}
        case RnDecision.Blocking{}:
          RnDecision.Waits{}

# LAW run_prepare_is_the_rust_rule: what preparation does, for every generation and every threshold,
# is what `before_request` did
law run_prepare_is_the_rust_rule:
  for +compacted: Bool
  for +th: RnDecision.Th
  {RnDecision.decide.prepare(compacted, th) == rust.before_request(compacted, th) : RnDecision.Prepared}

# LAW run_prepare_compacted_reads_no_threshold: a generation that compacted reads no threshold: whatever its
# context is over, it prepares as if under every threshold. So Rust need
# not measure the context (a provider's count is a request) after the
# generation compacted
law run_prepare_compacted_reads_no_threshold:
  for +th: RnDecision.Th
  {RnDecision.decide.prepare(True{}, th) == RnDecision.decide.prepare(True{}, RnDecision.Under{}) : RnDecision.Prepared}

# `after_compaction`: an entry goes on; a threshold compaction that
# found nothing goes on; an overflow's that found nothing, or any that
# failed, fails the run
def rust.after_compaction(over: Bool, got: RnState.Got) -> Bool:
  match over got:
    case over RnState.Built{}:
      True{}
    case True{} RnState.Kept{}:
      False{}
    case False{} RnState.Kept{}:
      True{}
    case over RnState.Broke{}:
      False{}

# LAW run_compact_is_the_rust_rule: whether preparation goes on after any compaction is what
# `after_compaction` decided
law run_compact_is_the_rust_rule:
  for +over: Bool
  for +got: RnState.Got
  {RnDecision.decide.compact(over, got) == rust.after_compaction(over, got) : Bool}

# a round that the cap lets go on hands the run on with one more round,
# unless a queued reset ends it
def rust.next(goes: Bool, reset: Bool, count: Nat) -> RnDecision.End:
  match goes:
    case True{}:
      match reset:
        case True{}:
          RnDecision.EndReset{}
        case False{}:
          RnDecision.EndNext{1n+count}
    case False{}:
      RnDecision.EndCapped{}

# `Rounds::finish` then `RoundEnd::reset`: a control stops the run; else
# the round after count rounds is capped at maxToolRounds
def rust.round_end(l: RnDecision.Lim, +count: Nat, stops: Bool, reset: Bool) -> RnDecision.End:
  match l:
    case RnDecision.Lim{rounds, wait, retries, most}:
      match stops:
        case True{}:
          RnDecision.EndStop{}
        case False{}:
          rust.next(Nat.is_lt(1n+count, rounds), reset, count)

# LAW run_round_is_the_rust_rule: how any round ends, after any rounds, under any cap, is what
# `Rounds::finish` and `RoundEnd::reset` decided
law run_round_is_the_rust_rule:
  for +l: RnDecision.Lim
  for +count: Nat
  for +stops: Bool
  for +reset: Bool
  {RnDecision.decide.round(l, count, stops, reset) == rust.round_end(l, count, stops, reset) : RnDecision.End}

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

# maxToolRounds, the ms a deferred job may run (a poll spends 1 ms),
# retry.maxRetries, MAX_NOTES and one

# ---- recover ----

# LAWS (H4.8): a stuck model gets a recovery. Each law is an open claim
# about the model in bend/run/recovery.bend; PROOF.bend proves them (as Run.<law>)
# with the lemmas of proof/run/.

# (H4.8) A stuck model gets a recovery, each with a cap
# -----------------------------------------------------
# LAWS.bend H4.8, the recoveries of bend/run/recovery.bend (Rec): a length
# stop while the model still reasons, tool calls leaked as text, the same
# tool calls with the same results round after round. Every reply is
# free, in any order. A Redo is a noted error, so its retry ends its
# request with a new note (H4.7); the laws of H4 hold for every reply, so
# they hold for the reply a recovery makes. A recovery does not depend on
# the retry policy: a note is a new request, not a transient error.

# LAW rec_length_gives_up: after `long` length notes in a row, a length stop fails the run
law rec_length_gives_up:
  for +rc: RnRecovery.RCfg
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for over: {RnRecovery.below(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc)) == False{} : Bool}
  {RnRecovery.Dec.act(RnRecovery.Rec.step(rc, RnRecovery.Long{}, RnRecovery.Rec{k, row, same, last})) == RnRecovery.Quit{} : RnRecovery.Act}

# LAW rec_leak_rebuilt_is_calls: leaked calls that every parse and name an offered tool are rebuilt:
# the run reads them as the same calls made as tool calls
law rec_leak_rebuilt_is_calls:
  for +rc: RnRecovery.RCfg
  for +h: Nat
  for kept: Bool
  for r: RnRecovery.Rec
  {RnRecovery.Rec.step(rc, RnRecovery.Leak{True{}, h, kept}, r) == RnRecovery.Rec.step(rc, RnRecovery.Ran{h, kept}, r) : RnRecovery.Dec}

# LAW rec_leak_stands: after `leak` leak notes in a row, the reply answers as text
law rec_leak_stands:
  for +rc: RnRecovery.RCfg
  for +h: Nat
  for kept: Bool
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for over: {RnRecovery.below(RnRecovery.Rk.leaks(k, row), RnRecovery.RCfg.leak(rc)) == False{} : Bool}
  {RnRecovery.Dec.act(RnRecovery.Rec.step(rc, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{k, row, same, last})) == RnRecovery.Stand{} : RnRecovery.Act}

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

# LAW rec_repeat_never_runs: tool calls that would make `repeat` rounds in a row with the same
# results never run
law rec_repeat_never_runs:
  for +rc: RnRecovery.RCfg
  for +h: Nat
  for kept: Bool
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for rep: {RnRecovery.below(RnRecovery.again(same, last, h), RnRecovery.RCfg.repeat(rc)) == False{} : Bool}
  {RnRecovery.Act.runs(RnRecovery.Dec.act(RnRecovery.Rec.step(rc, RnRecovery.Ran{h, kept}, RnRecovery.Rec{k, row, same, last}))) == False{} : Bool}

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

# LAW rec_repeat_gives_up: after `redirect` redirect notes in a row, a repeat fails the run
law rec_repeat_gives_up:
  for +rc: RnRecovery.RCfg
  for +h: Nat
  for kept: Bool
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for rep: {RnRecovery.below(RnRecovery.again(same, last, h), RnRecovery.RCfg.repeat(rc)) == False{} : Bool}
  for over: {RnRecovery.below(RnRecovery.Rk.loops(k, row), RnRecovery.RCfg.redirect(rc)) == False{} : Bool}
  {RnRecovery.Dec.act(RnRecovery.Rec.step(rc, RnRecovery.Ran{h, kept}, RnRecovery.Rec{k, row, same, last})) == RnRecovery.Quit{} : RnRecovery.Act}

# LAW rec_user_breaks_the_row: a user message ends the row: after it, no call is a repeat of a
# call before it
law rec_user_breaks_the_row:
  for +rc: RnRecovery.RCfg
  for +k: RnRecovery.Rk
  for +row: Nat
  for same: Nat
  for +last: Nat
  {RnRecovery.Dec.r(RnRecovery.Rec.step(rc, RnRecovery.Said{}, RnRecovery.Rec{k, row, same, last})) == RnRecovery.Rec{k, row, 0n, last} : RnRecovery.Rec}

# LAW rec_notes_capped: after any replies, the notes of a recovery in a row are at most
# its cap: every recovery stops at its cap
law rec_notes_capped:
  for +rc: RnRecovery.RCfg
  for +os: List<&2, RnRecovery.Out>
  {RnRecovery.Rec.capped(rc, RnRecovery.Rec.run(rc, os)) == True{} : Bool}

# LAW rec_never_runs_a_repeat: after any replies, the run has not run the same calls with the
# same results max(repeat, 1) rounds in a row. This replaces the loop
# guard of H4.3 (a run failed after LOOP_ROUNDS = 6 such rounds): it is
# stronger, as no such row ever reaches `repeat` (5) rounds
law rec_never_runs_a_repeat:
  for +rc: RnRecovery.RCfg
  for +os: List<&2, RnRecovery.Out>
  {RnRecovery.below(RnRecovery.Rec.same(RnRecovery.Rec.run(rc, os)), Nat.max(RnRecovery.RCfg.repeat(rc), 1n)) == True{} : Bool}

# LAW rec_stuck_gets_help: the harness never just watches a stuck model: a stuck reply (a
# length stop with no answer, leaked tool calls, tool calls) always gets
# an act that does something: its calls run (no repeat), a retry with a
# note, an answer, or the end of the run. It is never passed on as it is
law rec_stuck_gets_help:
  for +rc: RnRecovery.RCfg
  for o: RnRecovery.Out
  for r: RnRecovery.Rec
  {Bool.or(Bool.not(RnRecovery.Out.stuck(o)), RnRecovery.Act.helps(RnRecovery.Dec.act(RnRecovery.Rec.step(rc, o, r)))) == True{} : Bool}

# LAW rec_redo_is_noted: a recovery's retry is a noted error, so its request ends with the
# note of the next attempt (run_cut_names_the_request): it never sends
# the request again (run_retry_sends_a_new_request)
law rec_redo_is_noted:
  for -pass: RnState.Reply
  {RnRecovery.Act.reply(RnRecovery.Redo{}, pass) == RnState.Error{False{}, True{}} : RnState.Reply}

# LAW rec_quit_fails: a recovery at its cap fails the run on the model, at once
law rec_quit_fails:
  for +cfg: RnState.Cfg
  for -pass: RnState.Reply
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +n: Nat
  for +p: Nat
  {RnStep.call(cfg, RnRecovery.Act.reply(RnRecovery.Quit{}, pass), r, c, a, n, p) == RnState.St{RnState.Failed{RnState.Model{}}, r, c, a, n, p} : RnState.St}

# The recovery Rust calls (decide.rs `recover`, through the compiled
# core) is decide.recover of bend/run/decision.bend: the recoveries above (Rec.go)
# reading the stuck reply and the note's row as Rust has them. The
# helpers rust.* are `recover` as decide.rs wrote it: the row of each
# recovery that the request's note counts (`NoteCause::row`), its cap,
# and the rounds in a row of calls against REPEAT_CALLS.

# the length notes, leak notes and redirect notes in a row that a note of
# recovery k with row `row` makes
def rust.long_row(k: RnRecovery.Rk, row: Nat) -> Nat:
  match k:
    case RnRecovery.Free{}:
      0n
    case RnRecovery.Longs{}:
      row
    case RnRecovery.Leaks{}:
      0n
    case RnRecovery.Loops{}:
      0n

def rust.leak_row(k: RnRecovery.Rk, row: Nat) -> Nat:
  match k:
    case RnRecovery.Free{}:
      0n
    case RnRecovery.Longs{}:
      0n
    case RnRecovery.Leaks{}:
      row
    case RnRecovery.Loops{}:
      0n

def rust.loop_row(k: RnRecovery.Rk, row: Nat) -> Nat:
  match k:
    case RnRecovery.Free{}:
      0n
    case RnRecovery.Longs{}:
      0n
    case RnRecovery.Leaks{}:
      0n
    case RnRecovery.Loops{}:
      row

# under the cap a retry with the next note of the recovery; at it, cap
def rust.redo(under: Bool, row: Nat, cap: RnDecision.Help) -> RnDecision.Help:
  match under:
    case True{}:
      RnDecision.Redoes{1n+row}
    case False{}:
      cap

# calls below REPEAT_CALLS rounds in a row run; else the other act
def rust.calls(fresh: Bool, other: RnDecision.Help) -> RnDecision.Help:
  match fresh:
    case True{}:
      RnDecision.Runs{}
    case False{}:
      other

# `recover`
def rust.recover(rc: RnRecovery.RCfg, s: RnDecision.Stuck, +k: RnRecovery.Rk, +row: Nat) -> RnDecision.Help:
  match rc:
    case RnRecovery.RCfg{long, leak, redirect, repeat}:
      match s:
        case RnDecision.Truncated{}:
          rust.redo(Nat.is_lt(rust.long_row(k, row), long), rust.long_row(k, row), RnDecision.Quits{})
        case RnDecision.Leaked{}:
          rust.redo(Nat.is_lt(rust.leak_row(k, row), leak), rust.leak_row(k, row), RnDecision.Stands{})
        case RnDecision.Repeats{before}:
          rust.calls(Nat.is_lt(1n+before, repeat), rust.redo(Nat.is_lt(rust.loop_row(k, row), redirect), rust.loop_row(k, row), RnDecision.Quits{}))

# LAW rec_recover_is_the_rust_rule: what a recovery does with any stuck reply, after any note, under
# any caps, is what `recover` did: the code that runs is the recoveries
# whose laws are above
law rec_recover_is_the_rust_rule:
  for +rc: RnRecovery.RCfg
  for +s: RnDecision.Stuck
  for +k: RnRecovery.Rk
  for +row: Nat
  {RnDecision.decide.recover(rc, s, k, row) == rust.recover(rc, s, k, row) : RnDecision.Help}

# ---- run_ffi ----

# LAWS (H4.10): the entry of the run's decisions in the compiled core
# (bend/ffi_run.bend). Each law is an open claim; PROOF.bend proves them
# (as Run.<law>) in proof/run/ from the laws of laws/wire.bend.
# bend/ffi_run.bend: Rust writes a request (the decision's tag and its
# inputs) with eukhe_bend::wire::Writer, and reads the decision's value
# from the answer. Its codec composes the primitives of bend/wire.bend, so
# these laws rest on laws/wire.bend.

# Every Nat of a request fits the wire (at most 14 digits: Rust saturates
# its u64 counts at eukhe_bend::wire::NAT_MAX and its u32s fit)
def run.lim_fits(l: RnDecision.Lim) -> Bool:
  match l:
    case RnDecision.Lim{rounds, wait, retries, notes}:
      Bool.and(LawsBase.wire_fits(rounds), Bool.and(LawsBase.wire_fits(wait), Bool.and(LawsBase.wire_fits(retries), LawsBase.wire_fits(notes))))

def run.at_fits(t: RnDecision.At) -> Bool:
  match t:
    case RnDecision.At{attempt, notes, waited, compacted}:
      Bool.and(LawsBase.wire_fits(attempt), Bool.and(LawsBase.wire_fits(notes), LawsBase.wire_fits(waited)))

def run.rcfg_fits(c: RnRecovery.RCfg) -> Bool:
  match c:
    case RnRecovery.RCfg{long, leak, redirect, repeat}:
      Bool.and(LawsBase.wire_fits(long), Bool.and(LawsBase.wire_fits(leak), Bool.and(LawsBase.wire_fits(redirect), LawsBase.wire_fits(repeat))))

def run.stuck_fits(s: RnDecision.Stuck) -> Bool:
  match s:
    case RnDecision.Truncated{}:
      True{}
    case RnDecision.Leaked{}:
      True{}
    case RnDecision.Repeats{before}:
      LawsBase.wire_fits(before)

def run.ask_fits(a: FRn.Ask) -> Bool:
  match a:
    case FRn.AskReply{l, t, reply}:
      Bool.and(run.lim_fits(l), run.at_fits(t))
    case FRn.AskEnded{m}:
      True{}
    case FRn.AskPrepare{compacted, th}:
      True{}
    case FRn.AskCompact{over, got}:
      True{}
    case FRn.AskRound{l, count, stops, reset}:
      Bool.and(run.lim_fits(l), LawsBase.wire_fits(count))
    case FRn.AskRecover{rc, s, k, row}:
      Bool.and(run.rcfg_fits(rc), Bool.and(run.stuck_fits(s), LawsBase.wire_fits(row)))
    case FRn.AskPoll{retryable, failures, retries}:
      Bool.and(LawsBase.wire_fits(failures), LawsBase.wire_fits(retries))

# Every Nat of an answer fits the wire
def run.end_fits(e: RnDecision.End) -> Bool:
  match e:
    case RnDecision.EndStop{}:
      True{}
    case RnDecision.EndReset{}:
      True{}
    case RnDecision.EndCapped{}:
      True{}
    case RnDecision.EndNext{count}:
      LawsBase.wire_fits(count)

def run.help_fits(h: RnDecision.Help) -> Bool:
  match h:
    case RnDecision.Runs{}:
      True{}
    case RnDecision.Redoes{row}:
      LawsBase.wire_fits(row)
    case RnDecision.Stands{}:
      True{}
    case RnDecision.Quits{}:
      True{}

# LAW run_ffi_ask_round_trip: every request whose Nats fit the wire reads back as itself, and its
# reading consumes exactly its encoding
# EXCLUDES: a field read into another, a wrong tag, a lost or eaten rest
law run_ffi_ask_round_trip:
  for +a: FRn.Ask
  for +rest: String
  for +h: {run.ask_fits(a) == True{} : Bool}
  {FRn.get_ask(FRn.put_ask(a, rest)) == Wr.Got{a, rest} : Wr.Dec<FRn.Ask>}

# LAW run_ffi_ask_fits_witness: witness: a request whose Nats fit the wire exists
law run_ffi_ask_fits_witness:
  exs a: FRn.Ask
  {run.ask_fits(a) == True{} : Bool}

# LAW run_ffi_answers: the entry answers a request with the value of its decision
# EXCLUDES: an entry that answers another decision, or a default
law run_ffi_answers:
  for +a: FRn.Ask
  for +h: {run.ask_fits(a) == True{} : Bool}
  {FRn.ffi(FRn.put_ask(a, "")) == FRn.answer(a) : String}

# LAW run_ffi_refuses_left_over: a request with input left over after it is refused
# EXCLUDES: trailing input read as part of a request, or ignored
law run_ffi_refuses_left_over:
  for +a: FRn.Ask
  for +rest: String
  for +h: {run.ask_fits(a) == True{} : Bool}
  for +more: {String.is_empty(rest) == False{} : Bool}
  {FRn.ffi(FRn.put_ask(a, rest)) == Wr.err("run: input left over after the request") : String}

# LAW run_ffi_left_over_witness: witness: input is left over after a request
law run_ffi_left_over_witness:
  exs rest: String
  {String.is_empty(rest) == False{} : Bool}

# LAW run_ffi_refuses_malformed: a malformed request answers the error form, never a decision
# EXCLUDES: a default decision for input the entry cannot read
law run_ffi_refuses_malformed:
  for +s: String
  for +bad: {FRn.get_ask(s) == Wr.Bad{} : Wr.Dec<FRn.Ask>}
  {FRn.ffi(s) == Wr.err("run: malformed request") : String}

# LAW run_ffi_malformed_witness: witness: a malformed request exists
law run_ffi_malformed_witness:
  exs s: String
  {FRn.get_ask(s) == Wr.Bad{} : Wr.Dec<FRn.Ask>}

# LAW run_ffi_then_round_trip: every answer reads back as itself: the step after a reply, what
# preparation does, how a round ends, what a recovery does, the reply a
# message makes (Rust's Reader reads the same grammar)
# EXCLUDES: two answers with one encoding, an answer Rust misreads
law run_ffi_then_round_trip:
  for +x: RnDecision.Then
  for +rest: String
  {FRn.get_then(FRn.put_then(x, rest)) == Wr.Got{x, rest} : Wr.Dec<RnDecision.Then>}

# LAW run_ffi_prepared_round_trip: a prepared decision written to the wire reads back as itself; the rest of the input stays
law run_ffi_prepared_round_trip:
  for +x: RnDecision.Prepared
  for +rest: String
  {FRn.get_prepared(FRn.put_prepared(x, rest)) == Wr.Got{x, rest} : Wr.Dec<RnDecision.Prepared>}

# LAW run_ffi_end_round_trip: an end that fits the wire reads back as itself; the rest of the input stays
law run_ffi_end_round_trip:
  for +x: RnDecision.End
  for +rest: String
  for +h: {run.end_fits(x) == True{} : Bool}
  {FRn.get_end(FRn.put_end(x, rest)) == Wr.Got{x, rest} : Wr.Dec<RnDecision.End>}

# LAW run_ffi_help_round_trip: a help request that fits the wire reads back as itself; the rest of the input stays
law run_ffi_help_round_trip:
  for +x: RnDecision.Help
  for +rest: String
  for +h: {run.help_fits(x) == True{} : Bool}
  {FRn.get_help(FRn.put_help(x, rest)) == Wr.Got{x, rest} : Wr.Dec<RnDecision.Help>}

# LAW run_ffi_reply_round_trip: a reply written to the wire reads back as itself; the rest of the input stays
law run_ffi_reply_round_trip:
  for +x: RnState.Reply
  for +rest: String
  {FRn.get_reply(FRn.put_reply(x, rest)) == Wr.Got{x, rest} : Wr.Dec<RnState.Reply>}

# LAW run_ffi_answer_fits_witness: witness: answers whose Nats fit the wire exist
law run_ffi_answer_fits_witness:
  exs e: RnDecision.End
  exs x: RnDecision.Help
  {Bool.and(run.end_fits(e), run.help_fits(x)) == True{} : Bool}
