# eukhe: the laws of area run

import Base
import ../bend/ffi_run.bend as FRn
import ../bend/retry.bend as R
import ../bend/run.bend as Rn
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (H4) Every run ends
# -------------------
# docs/harness.md H4, the model in bend/run.bend: one run (one user turn)
# through prepare, call (a request or a deferred poll), compact (an
# overflow's or a blocking threshold one) and tools. Every input is free:
# any model reply, any round end, any compaction result, an abort, in any
# order.

# LAW: every run has ended (answered, aborted or failed) after bound(cfg)
# inputs, whatever they are and whatever follows them; bound(cfg) =
# max(cap, 1)·(2 + (retries + notes + 2)·(polls + 2)), from
# compaction a generation. Notes have their own budget: a noted retry
# spends a note, never a retry
law run_ends:
  for +cfg: Rn.Cfg
  for +evs: List<&2, Rn.Ev>
  for long: {List.length(&2, Rn.Ev, evs) == Rn.bound(cfg) : Nat}
  for +more: List<&2, Rn.Ev>
  {Rn.done(Rn.run(cfg, List.append(&2, Rn.Ev, evs, more))) == True{} : Bool}

# LAW: an ended run stays as it ended
law run_end_stays:
  for +cfg: Rn.Cfg
  for +s: Rn.St
  for ended: {Rn.done(s) == True{} : Bool}
  for +e: Rn.Ev
  {Rn.step(cfg, s, e) == s : Rn.St}

# LAW: an abort ends a live run as aborted, at the next step
law run_abort_ends_now:
  for +cfg: Rn.Cfg
  for +s: Rn.St
  for live: {Rn.done(s) == False{} : Bool}
  {Rn.St.ph(Rn.step(cfg, s, Rn.Abort{})) == Rn.Aborted{} : Rn.Ph}

# LAW: a run that has made max(cap, 1) tool rounds has failed
law run_rounds_capped:
  for +cfg: Rn.Cfg
  for +evs: List<&2, Rn.Ev>
  Or({Rn.failed(Rn.run(cfg, evs)) == True{} : Bool}, {Nat.is_lt(Rn.rounds(cfg, evs), Nat.max(Rn.Cfg.cap(cfg), 1n)) == True{} : Bool})

# The loop guard of H4.3 (run_loop_needs_repeats) is gone. The law
# `rec_never_runs_a_repeat` (H4.8) replaces it, and it is stronger: no
# row of the same calls with the same results ever gets to REPEAT_CALLS
# (5) rounds. The loop guard failed a run only after 6 such rounds.

# LAW: the round cap fails a run only at its max(cap, 1)th round, never
# earlier
law run_rounds_fail_at_cap:
  for +cfg: Rn.Cfg
  for +evs: List<&2, Rn.Ev>
  Or({Rn.capped(Rn.run(cfg, evs)) == False{} : Bool}, {Rn.rounds(cfg, evs) == Nat.max(Rn.Cfg.cap(cfg), 1n) : Nat})

# LAW: the poll cap fails a run only when its request's reply and each of
# its `polls` polls were deferred, polls + 1 deferred replies in a row
law run_polls_need_defers:
  for +cfg: Rn.Cfg
  for +evs: List<&2, Rn.Ev>
  Or({Rn.polled(Rn.run(cfg, evs)) == False{} : Bool}, {Rn.defers(cfg, evs) == 1n+Rn.Cfg.polls(cfg) : Nat})

# LAW: a message that ends the model's turn (any stop reason) with no
# text and no tool call never answers the run (H4.7): the model gave no
# answer, so the step is a noted error's: a retry with a note while
# notes are left, else the run fails on the model
law run_no_answer_is_an_error:
  for +cfg: Rn.Cfg
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +n: Nat
  for +p: Nat
  {Rn.call(cfg, Rn.Ended.reply(Rn.Ended{False{}, False{}}), r, c, a, n, p) == Rn.note(cfg, r, c, a, n, p) : Rn.St}

# LAW: a message that ends the model's turn with a tool call never
# answers the run: its calls go to the tools phase, whatever its text and
# its stop reason. vLLM, llama.cpp and Ollama send the stop reason stop
# with tool calls
law run_calls_never_answer:
  for +cfg: Rn.Cfg
  for text: Bool
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +n: Nat
  for +p: Nat
  {Rn.call(cfg, Rn.Ended.reply(Rn.Ended{text, True{}}), r, c, a, n, p) == Rn.St{Rn.Tools{}, r, c, a, n, p} : Rn.St}

# LAW: a noted error spends a note, not a retry: retryable or not, it is
# retried with a note while notes are left, and the retries left stay
law run_note_spends_no_retry:
  for +cfg: Rn.Cfg
  for retryable: Bool
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +m: Nat
  for +p: Nat
  {Rn.call(cfg, Rn.Error{retryable, True{}}, r, c, a, 1n+m, p) == Rn.St{Rn.Prepare{}, r, c, a, m, Rn.Cfg.polls(cfg)} : Rn.St}

# LAW: a retryable error that is not noted spends a retry, not a note:
# the notes left stay
law run_retry_spends_no_note:
  for +cfg: Rn.Cfg
  for +r: Nat
  for +c: Nat
  for +b: Nat
  for +n: Nat
  for +p: Nat
  {Rn.call(cfg, Rn.Error{True{}, False{}}, r, c, 1n+b, n, p) == Rn.St{Rn.Prepare{}, r, c, b, n, Rn.Cfg.polls(cfg)} : Rn.St}

# (H4.7) A retry never resends a request it cut
# ---------------------------------------------
# docs/harness.md H4.7, the requests of bend/run.bend: a model decodes
# the same request the same way (a greedy one always does), so a retry
# after a noted reply (the stream repeated itself until the guard cut it,
# or the reply gave no answer) ends its request with a harness note that
# names the retry's attempt. A request is the version of its logged
# context and the attempt its note names.

# LAW: no request the run sends is equal to a request it sent before and
# had cut: a retry after a cut sends neither the request it cut nor any
# other one the run cut, whatever the inputs, cut after cut until the
# notes run out
law run_retry_sends_a_new_request:
  for +cfg: Rn.Cfg
  for +evs: List<&2, Rn.Ev>
  {Rn.fresh(Rn.Reqs.log(Rn.reqs(cfg, evs))) == True{} : Bool}

# LAW: a noted reply cuts the request the run sent, and the next request
# carries the note of the next attempt
law run_cut_names_the_request:
  for -retryable: Bool
  for -fin: Rn.Fin
  for -got: Rn.Got
  for -pa: Rn.Ph
  for -ctx: Nat
  for -n: Nat
  for -note: Nat
  for -log: List<&2, Rn.Sent>
  {Rn.Reqs.step(Rn.Call{}, Rn.Go{Rn.Error{retryable, True{}}, fin, got}, pa, Rn.Reqs{ctx, n, note, log}) == Rn.Reqs{ctx, 1n+n, 1n+n, Rn.Cut{Rn.Req{ctx, note}} <> log} : Rn.Reqs}

# LAW: the note changes what the model reads, never what the run logs:
# a request logs the same lines as its context with no note
law run_note_is_never_logged:
  for q: Rn.Req
  {Rn.logged(Rn.Req.lines(q)) == Rn.logged(Rn.Req.lines(Rn.Req{Rn.Req.ctx(q), 0n})) : List<&2, Rn.Line>}

# (H4.9) The decisions Rust calls are the model's
# -----------------------------------------------
# docs/harness.md H4, the decisions of bend/run.bend that
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
def rust.wait(waits: Bool) -> Rn.Then:
  match waits:
    case True{}:
      Rn.DoPoll{}
    case False{}:
      Rn.DoLate{}

# a noted reply retries with a note while notes are left
def rust.noted(left: Bool) -> Rn.Then:
  match left:
    case True{}:
      Rn.DoNote{}
    case False{}:
      Rn.DoFail{}

# an error that is not noted retries while it is retryable and retries
# are left
def rust.retry(left: Bool) -> Rn.Then:
  match left:
    case True{}:
      Rn.DoRetry{}
    case False{}:
      Rn.DoFail{}

# an overflow compacts when a cut exists and the generation has not
# compacted
def rust.over(compacts: Bool) -> Rn.Then:
  match compacts:
    case True{}:
      Rn.DoCompact{}
    case False{}:
      Rn.DoFail{}

# `after_reply`: the retries spent are the attempts after the first that
# were not noted, (attempt - 1) - notes
def rust.after_reply(l: Rn.Lim, t: Rn.At, reply: Rn.Reply) -> Rn.Then:
  match l:
    case Rn.Lim{rounds, wait, retries, most}:
      match t:
        case Rn.At{attempt, +notes, waited, compacted}:
          match reply:
            case Rn.Plain{}:
              Rn.DoAnswer{}
            case Rn.Calls{}:
              Rn.DoTools{}
            case Rn.Deferred{}:
              rust.wait(Nat.is_lt(waited, wait))
            case Rn.Error{retryable, noted}:
              match noted:
                case True{}:
                  rust.noted(Nat.is_lt(notes, most))
                case False{}:
                  rust.retry(Bool.and(retryable, Nat.is_lt(Nat.sub(Nat.sub(attempt, 1n), notes), retries)))
            case Rn.Overflow{cut}:
              rust.over(Bool.and(cut, Bool.not(compacted)))

# LAW: the step after any reply, from any counts and limits, is the one
# `after_reply` took: the counts left that the model reads (At.a, At.n,
# At.p, At.c) are exact
law run_reply_is_the_rust_rule:
  for +l: Rn.Lim
  for +t: Rn.At
  for +reply: Rn.Reply
  {Rn.decide.reply(l, t, reply) == rust.after_reply(l, t, reply) : Rn.Then}

# `before_request`: a generation that compacted sends its request with no
# compaction; else a context over the blocking threshold (with a cut)
# waits for a compaction, and one over the background threshold sends
# with a background compaction beside it
def rust.before_request(compacted: Bool, th: Rn.Th) -> Rn.Prepared:
  match compacted:
    case True{}:
      Rn.Sends{False{}}
    case False{}:
      match th:
        case Rn.Under{}:
          Rn.Sends{False{}}
        case Rn.Background{}:
          Rn.Sends{True{}}
        case Rn.Blocking{}:
          Rn.Waits{}

# LAW: what preparation does, for every generation and every threshold,
# is what `before_request` did
law run_prepare_is_the_rust_rule:
  for +compacted: Bool
  for +th: Rn.Th
  {Rn.decide.prepare(compacted, th) == rust.before_request(compacted, th) : Rn.Prepared}

# LAW: a generation that compacted reads no threshold: whatever its
# context is over, it prepares as if under every threshold. So Rust need
# not measure the context (a provider's count is a request) after the
# generation compacted
law run_prepare_compacted_reads_no_threshold:
  for +th: Rn.Th
  {Rn.decide.prepare(True{}, th) == Rn.decide.prepare(True{}, Rn.Under{}) : Rn.Prepared}

# `after_compaction`: an entry goes on; a threshold compaction that
# found nothing goes on; an overflow's that found nothing, or any that
# failed, fails the run
def rust.after_compaction(over: Bool, got: Rn.Got) -> Bool:
  match over got:
    case over Rn.Built{}:
      True{}
    case True{} Rn.Kept{}:
      False{}
    case False{} Rn.Kept{}:
      True{}
    case over Rn.Broke{}:
      False{}

# LAW: whether preparation goes on after any compaction is what
# `after_compaction` decided
law run_compact_is_the_rust_rule:
  for +over: Bool
  for +got: Rn.Got
  {Rn.decide.compact(over, got) == rust.after_compaction(over, got) : Bool}

# a round that the cap lets go on hands the run on with one more round,
# unless a queued reset ends it
def rust.next(goes: Bool, reset: Bool, count: Nat) -> Rn.End:
  match goes:
    case True{}:
      match reset:
        case True{}:
          Rn.EndReset{}
        case False{}:
          Rn.EndNext{1n+count}
    case False{}:
      Rn.EndCapped{}

# `Rounds::finish` then `RoundEnd::reset`: a control stops the run; else
# the round after count rounds is capped at maxToolRounds
def rust.round_end(l: Rn.Lim, +count: Nat, stops: Bool, reset: Bool) -> Rn.End:
  match l:
    case Rn.Lim{rounds, wait, retries, most}:
      match stops:
        case True{}:
          Rn.EndStop{}
        case False{}:
          rust.next(Nat.is_lt(1n+count, rounds), reset, count)

# LAW: how any round ends, after any rounds, under any cap, is what
# `Rounds::finish` and `RoundEnd::reset` decided
law run_round_is_the_rust_rule:
  for +l: Rn.Lim
  for +count: Nat
  for +stops: Bool
  for +reset: Bool
  {Rn.decide.round(l, count, stops, reset) == rust.round_end(l, count, stops, reset) : Rn.End}

# LAW: a round that no control stops leaves the rounds left of the run of
# count + 1 rounds: the model counts down as Rust counts up
law run_round_counts_down:
  for +l: Rn.Lim
  for +count: Nat
  for +reset: Bool
  for +c: Nat
  for +a: Nat
  for +n: Nat
  for +p: Nat
  {Rn.St.r(Rn.tools(Rn.Lim.cfg(l), Rn.fin.of(False{}, reset), Rn.Lim.r(l, count), c, a, n, p)) == Rn.Lim.r(l, 1n+count) : Nat}

# the counts of the request a noted retry sends: one more attempt and
# one more note (`retry_note`, then the retry phase)
def rust.noted_next(t: Rn.At) -> Rn.At:
  match t:
    case Rn.At{attempt, notes, waited, compacted}:
      Rn.At{1n+attempt, 1n+notes, 0n, compacted}

# the counts of the request a transient retry sends: one more attempt
def rust.retried_next(t: Rn.At) -> Rn.At:
  match t:
    case Rn.At{attempt, notes, waited, compacted}:
      Rn.At{1n+attempt, notes, 0n, compacted}

# LAW: a noted reply leaves the notes left of the request its retry
# sends
law run_note_counts_down:
  for +l: Rn.Lim
  for +t: Rn.At
  for +r: Nat
  for +c: Nat
  for +p: Nat
  {Rn.St.n(Rn.note(Rn.Lim.cfg(l), r, c, Rn.At.a(l, t), Rn.At.n(l, t), p)) == Rn.At.n(l, rust.noted_next(t)) : Nat}

# LAW: a noted reply leaves the retries left of the request its retry
# sends: a note spends no retry
law run_note_keeps_the_retries:
  for +l: Rn.Lim
  for +t: Rn.At
  for +r: Nat
  for +c: Nat
  for +p: Nat
  {Rn.St.a(Rn.note(Rn.Lim.cfg(l), r, c, Rn.At.a(l, t), Rn.At.n(l, t), p)) == Rn.At.a(l, rust.noted_next(t)) : Nat}

# LAW: a retryable error leaves the retries left of the request its retry
# sends, for every request whose attempts count its notes (attempt >=
# 1 + notes, as every request of a generation has)
law run_retry_counts_down:
  for +l: Rn.Lim
  for +t: Rn.At
  for +e: {Nat.is_le(1n+Rn.At.notes(t), Rn.At.attempt(t)) == True{} : Bool}
  for +r: Nat
  for +c: Nat
  for +p: Nat
  {Rn.St.a(Rn.retry(Rn.Lim.cfg(l), True{}, r, c, Rn.At.a(l, t), Rn.At.n(l, t), p)) == Rn.At.a(l, rust.retried_next(t)) : Nat}

# LAW: witness: a request whose attempts count its notes exists
law run_retry_premise_witness:
  exs t: Rn.At
  {Nat.is_le(1n+Rn.At.notes(t), Rn.At.attempt(t)) == True{} : Bool}

# LAW: a retryable error leaves the notes left of the request its retry
# sends: a retry spends no note
law run_retry_keeps_the_notes:
  for +l: Rn.Lim
  for +t: Rn.At
  for +r: Nat
  for +c: Nat
  for +p: Nat
  {Rn.St.n(Rn.retry(Rn.Lim.cfg(l), True{}, r, c, Rn.At.a(l, t), Rn.At.n(l, t), p)) == Rn.At.n(l, rust.retried_next(t)) : Nat}

# the counts of a request within its limits: notes at most MAX_NOTES,
# an attempt per note and one more, retries spent at most
# retry.maxRetries, the ms waited at most the job's
def rust.within(l: Rn.Lim, t: Rn.At) -> Bool:
  match l:
    case Rn.Lim{rounds, wait, retries, most}:
      match t:
        case Rn.At{+attempt, +notes, waited, compacted}:
          Bool.and(Nat.is_le(notes, most), Bool.and(Nat.is_le(1n+notes, attempt), Bool.and(Nat.is_le(Nat.sub(Nat.sub(attempt, 1n), notes), retries), Nat.is_le(waited, wait))))

# the counts Rust keeps, read back from the counts left
def rust.back(l: Rn.Lim, a: Nat, +n: Nat, p: Nat, c: Nat) -> Rn.At:
  match l:
    case Rn.Lim{rounds, wait, retries, +most}:
      Rn.At{1n+Nat.add(Nat.sub(retries, a), Nat.sub(most, n)), Nat.sub(most, n), Nat.sub(wait, p), Nat.is_eq(c, 0n)}

# LAW: the counts left lose nothing: within its limits, a request's
# counts come back from the counts left the model reads
law run_counts_lossless:
  for +l: Rn.Lim
  for +t: Rn.At
  for +w: {rust.within(l, t) == True{} : Bool}
  {rust.back(l, Rn.At.a(l, t), Rn.At.n(l, t), Rn.At.p(l, t), Rn.At.c(t)) == t : Rn.At}

# LAW: witness: counts within their limits exist
law run_counts_within_witness:
  exs l: Rn.Lim
  exs t: Rn.At
  {rust.within(l, t) == True{} : Bool}

# LAW: the rounds left lose nothing: below the cap, the rounds made come
# back from the rounds left
law run_rounds_lossless:
  for +l: Rn.Lim
  for +count: Nat
  for +w: {Nat.is_lt(count, Rn.Lim.rounds(l)) == True{} : Bool}
  {Nat.sub(Nat.sub(Rn.Lim.rounds(l), 1n), Rn.Lim.r(l, count)) == count : Nat}

# LAW: witness: a run below its round cap exists
law run_rounds_within_witness:
  exs l: Rn.Lim
  exs count: Nat
  {Nat.is_lt(count, Rn.Lim.rounds(l)) == True{} : Bool}

# what a failed poll of a live job does in Rust: poll again when
# `PollFailure::next` repolls and the poll's time check (a deferred reply)
# polls; else cancel the job
def rust.job(repoll: Bool, t: Rn.Then) -> R.Act:
  match repoll:
    case True{}:
      match t:
        case Rn.DoPoll{}:
          R.Poll{}
        case Rn.DoAnswer{}:
          R.Cancel{}
        case Rn.DoTools{}:
          R.Cancel{}
        case Rn.DoRetry{}:
          R.Cancel{}
        case Rn.DoNote{}:
          R.Cancel{}
        case Rn.DoCompact{}:
          R.Cancel{}
        case Rn.DoFail{}:
          R.Cancel{}
        case Rn.DoLate{}:
          R.Cancel{}
    case False{}:
      R.Cancel{}

# what a deferred reply does to the job in Rust: poll again, or cancel it
# at its deadline
def rust.later(t: Rn.Then) -> R.Act:
  match t:
    case Rn.DoPoll{}:
      R.Poll{}
    case Rn.DoAnswer{}:
      R.Cancel{}
    case Rn.DoTools{}:
      R.Cancel{}
    case Rn.DoRetry{}:
      R.Cancel{}
    case Rn.DoNote{}:
      R.Cancel{}
    case Rn.DoCompact{}:
      R.Cancel{}
    case Rn.DoFail{}:
      R.Cancel{}
    case Rn.DoLate{}:
      R.Cancel{}

# LAW: a failed poll of a live job, from any counts, does what the job of
# bend/retry.bend section 4 does with the ms left (wait - waited): it
# polls the same job again exactly when that job does
law run_failed_poll_is_the_job_model:
  for +l: Rn.Lim
  for +t: Rn.At
  for +retryable: Bool
  for +failed: Nat
  for +budget: Nat
  for +gap: Nat
  {rust.job(Rn.decide.poll(retryable, failed, Rn.Lim.retries(l)), Rn.decide.reply(l, t, Rn.Deferred{})) == R.Step.act(R.step(Rn.Lim.retries(l), budget, R.Live{failed, Rn.At.p(l, t)}, R.Broke{retryable, gap})) : R.Act}

# LAW: a deferred reply to a poll of a live job, from any counts, does
# what the job of bend/retry.bend section 4 does with the ms left: it
# polls again exactly when that job does, else the job is cancelled at
# its deadline
law run_deferred_reply_is_the_job_model:
  for +l: Rn.Lim
  for +t: Rn.At
  for +fails: Nat
  for +budget: Nat
  for +failed: Nat
  for +gap: Nat
  {rust.later(Rn.decide.reply(l, t, Rn.Deferred{})) == R.Step.act(R.step(fails, budget, R.Live{failed, Rn.At.p(l, t)}, R.Later{gap})) : R.Act}

# LAW: the first deferred reply of a request does what the job of
# bend/retry.bend section 4 does with a new job of the ms left
law run_first_deferred_reply_is_the_job_model:
  for +l: Rn.Lim
  for +t: Rn.At
  for +fails: Nat
  for +gap: Nat
  {rust.later(Rn.decide.reply(l, t, Rn.Deferred{})) == R.Step.act(R.step(fails, Rn.At.p(l, t), R.NoJob{}, R.Later{gap})) : R.Act}

# the limits with the job's ms saturated at cap
def rust.sat_wait(l: Rn.Lim, +cap: Nat) -> Rn.Lim:
  match l:
    case Rn.Lim{rounds, wait, retries, most}:
      Rn.Lim{rounds, Nat.min(wait, cap), retries, most}

# the counts with the attempt saturated at cap
def rust.sat_attempt(t: Rn.At, +cap: Nat) -> Rn.At:
  match t:
    case Rn.At{attempt, notes, waited, compacted}:
      Rn.At{Nat.min(attempt, cap), notes, waited, compacted}

# LAW: Rust saturates the job's ms and the ms waited (u64s) at the wire's
# largest Nat (10^14 - 1) before it encodes them: for a request that
# waited less than any cap (10^14 ms is 3000 years), the step after any
# reply is the same. A wait at the cap never ends a job that waited less
law run_reply_saturates_the_wait:
  for +l: Rn.Lim
  for +t: Rn.At
  for +reply: Rn.Reply
  for +cap: Nat
  for +e: {Nat.is_lt(Rn.At.waited(t), cap) == True{} : Bool}
  {Rn.decide.reply(rust.sat_wait(l, cap), t, reply) == Rn.decide.reply(l, t, reply) : Rn.Then}

# LAW: Rust saturates the attempt (a u64) at the wire's largest Nat: any
# cap above notes + retry.maxRetries (two u32s) leaves the step after any
# reply the same (an attempt at the cap has spent every retry, as a
# larger one)
law run_reply_saturates_the_attempt:
  for +l: Rn.Lim
  for +t: Rn.At
  for +reply: Rn.Reply
  for +cap: Nat
  for +e: {Nat.is_lt(Nat.add(Rn.At.notes(t), Rn.Lim.retries(l)), cap) == True{} : Bool}
  {Rn.decide.reply(l, rust.sat_attempt(t, cap), reply) == Rn.decide.reply(l, t, reply) : Rn.Then}

# maxToolRounds, the ms a deferred job may run (a poll spends 1 ms),
# retry.maxRetries, MAX_NOTES and one

# ---- recover ----

# LAWS (H4.8): a stuck model gets a recovery. Each law is an open claim
# about the model in bend/run.bend; PROOF.bend proves them (as Laws.<law>)
# with the lemmas of PROOF.bend section recover.

# (H4.8) A stuck model gets a recovery, each with a cap
# -----------------------------------------------------
# docs/harness.md H4.8, the recoveries of bend/run.bend (Rec): a length
# stop while the model still reasons, tool calls leaked as text, the same
# tool calls with the same results round after round. Every reply is
# free, in any order. A Redo is a noted error, so its retry ends its
# request with a new note (H4.7); the laws of H4 hold for every reply, so
# they hold for the reply a recovery makes. A recovery does not depend on
# the retry policy: a note is a new request, not a transient error.

# LAW: after `long` length notes in a row, a length stop fails the run
law rec_length_gives_up:
  for +rc: Rn.RCfg
  for +k: Rn.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for over: {Rn.below(Rn.Rk.longs(k, row), Rn.RCfg.long(rc)) == False{} : Bool}
  {Rn.Dec.act(Rn.Rec.step(rc, Rn.Long{}, Rn.Rec{k, row, same, last})) == Rn.Quit{} : Rn.Act}

# LAW: leaked calls that every parse and name an offered tool are rebuilt:
# the run reads them as the same calls made as tool calls
law rec_leak_rebuilt_is_calls:
  for +rc: Rn.RCfg
  for +h: Nat
  for kept: Bool
  for r: Rn.Rec
  {Rn.Rec.step(rc, Rn.Leak{True{}, h, kept}, r) == Rn.Rec.step(rc, Rn.Ran{h, kept}, r) : Rn.Dec}

# LAW: after `leak` leak notes in a row, the reply answers as text
law rec_leak_stands:
  for +rc: Rn.RCfg
  for +h: Nat
  for kept: Bool
  for +k: Rn.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for over: {Rn.below(Rn.Rk.leaks(k, row), Rn.RCfg.leak(rc)) == False{} : Bool}
  {Rn.Dec.act(Rn.Rec.step(rc, Rn.Leak{False{}, h, kept}, Rn.Rec{k, row, same, last})) == Rn.Stand{} : Rn.Act}

# LAW: tool calls that make fewer than `repeat` rounds in a row run: the
# recoveries never stop a call that is not a repeat. The rounds in a row
# grow when the results are those of the last round; when the results
# change (a poll of a job that makes progress), a new row of 1 starts
law rec_calls_run:
  for +rc: Rn.RCfg
  for +h: Nat
  for +kept: Bool
  for +k: Rn.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for fresh: {Rn.below(Rn.again(same, last, h), Rn.RCfg.repeat(rc)) == True{} : Bool}
  {Rn.Rec.step(rc, Rn.Ran{h, kept}, Rn.Rec{k, row, same, last}) == Rn.Dec{Rn.Exec{}, Rn.Rec{Rn.Free{}, 0n, Rn.ran.same(kept, Rn.again(same, last, h)), h}} : Rn.Dec}

# LAW: tool calls that would make `repeat` rounds in a row with the same
# results never run
law rec_repeat_never_runs:
  for +rc: Rn.RCfg
  for +h: Nat
  for kept: Bool
  for +k: Rn.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for rep: {Rn.below(Rn.again(same, last, h), Rn.RCfg.repeat(rc)) == False{} : Bool}
  {Rn.Act.runs(Rn.Dec.act(Rn.Rec.step(rc, Rn.Ran{h, kept}, Rn.Rec{k, row, same, last}))) == False{} : Bool}

# LAW: such a repeat, under the cap, is retried with the next redirect
# note
law rec_repeat_redirects:
  for +rc: Rn.RCfg
  for +h: Nat
  for kept: Bool
  for +k: Rn.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for rep: {Rn.below(Rn.again(same, last, h), Rn.RCfg.repeat(rc)) == False{} : Bool}
  for under: {Rn.below(Rn.Rk.loops(k, row), Rn.RCfg.redirect(rc)) == True{} : Bool}
  {Rn.Rec.step(rc, Rn.Ran{h, kept}, Rn.Rec{k, row, same, last}) == Rn.Dec{Rn.Redo{}, Rn.Rec{Rn.Loops{}, 1n+Rn.Rk.loops(k, row), same, last}} : Rn.Dec}

# LAW: after `redirect` redirect notes in a row, a repeat fails the run
law rec_repeat_gives_up:
  for +rc: Rn.RCfg
  for +h: Nat
  for kept: Bool
  for +k: Rn.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for rep: {Rn.below(Rn.again(same, last, h), Rn.RCfg.repeat(rc)) == False{} : Bool}
  for over: {Rn.below(Rn.Rk.loops(k, row), Rn.RCfg.redirect(rc)) == False{} : Bool}
  {Rn.Dec.act(Rn.Rec.step(rc, Rn.Ran{h, kept}, Rn.Rec{k, row, same, last})) == Rn.Quit{} : Rn.Act}

# LAW: a user message ends the row: after it, no call is a repeat of a
# call before it
law rec_user_breaks_the_row:
  for +rc: Rn.RCfg
  for +k: Rn.Rk
  for +row: Nat
  for same: Nat
  for +last: Nat
  {Rn.Dec.r(Rn.Rec.step(rc, Rn.Said{}, Rn.Rec{k, row, same, last})) == Rn.Rec{k, row, 0n, last} : Rn.Rec}

# LAW: after any replies, the notes of a recovery in a row are at most
# its cap: every recovery stops at its cap
law rec_notes_capped:
  for +rc: Rn.RCfg
  for +os: List<&2, Rn.Out>
  {Rn.Rec.capped(rc, Rn.Rec.run(rc, os)) == True{} : Bool}

# LAW: after any replies, the run has not run the same calls with the
# same results max(repeat, 1) rounds in a row. This replaces the loop
# guard of H4.3 (a run failed after LOOP_ROUNDS = 6 such rounds): it is
# stronger, as no such row ever reaches `repeat` (5) rounds
law rec_never_runs_a_repeat:
  for +rc: Rn.RCfg
  for +os: List<&2, Rn.Out>
  {Rn.below(Rn.Rec.same(Rn.Rec.run(rc, os)), Nat.max(Rn.RCfg.repeat(rc), 1n)) == True{} : Bool}

# LAW: the harness never just watches a stuck model: a stuck reply (a
# length stop with no answer, leaked tool calls, tool calls) always gets
# an act that does something: its calls run (no repeat), a retry with a
# note, an answer, or the end of the run. It is never passed on as it is
law rec_stuck_gets_help:
  for +rc: Rn.RCfg
  for o: Rn.Out
  for r: Rn.Rec
  {Bool.or(Bool.not(Rn.Out.stuck(o)), Rn.Act.helps(Rn.Dec.act(Rn.Rec.step(rc, o, r)))) == True{} : Bool}

# LAW: a recovery's retry is a noted error, so its request ends with the
# note of the next attempt (run_cut_names_the_request): it never sends
# the request again (run_retry_sends_a_new_request)
law rec_redo_is_noted:
  for -pass: Rn.Reply
  {Rn.Act.reply(Rn.Redo{}, pass) == Rn.Error{False{}, True{}} : Rn.Reply}

# LAW: a recovery at its cap fails the run on the model, at once
law rec_quit_fails:
  for +cfg: Rn.Cfg
  for -pass: Rn.Reply
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +n: Nat
  for +p: Nat
  {Rn.call(cfg, Rn.Act.reply(Rn.Quit{}, pass), r, c, a, n, p) == Rn.St{Rn.Failed{Rn.Model{}}, r, c, a, n, p} : Rn.St}

# The recovery Rust calls (decide.rs `recover`, through the compiled
# core) is decide.recover of bend/run.bend: the recoveries above (Rec.go)
# reading the stuck reply and the note's row as Rust has them. The
# helpers rust.* are `recover` as decide.rs wrote it: the row of each
# recovery that the request's note counts (`NoteCause::row`), its cap,
# and the rounds in a row of calls against REPEAT_CALLS.

# the length notes, leak notes and redirect notes in a row that a note of
# recovery k with row `row` makes
def rust.long_row(k: Rn.Rk, row: Nat) -> Nat:
  match k:
    case Rn.Free{}:
      0n
    case Rn.Longs{}:
      row
    case Rn.Leaks{}:
      0n
    case Rn.Loops{}:
      0n

def rust.leak_row(k: Rn.Rk, row: Nat) -> Nat:
  match k:
    case Rn.Free{}:
      0n
    case Rn.Longs{}:
      0n
    case Rn.Leaks{}:
      row
    case Rn.Loops{}:
      0n

def rust.loop_row(k: Rn.Rk, row: Nat) -> Nat:
  match k:
    case Rn.Free{}:
      0n
    case Rn.Longs{}:
      0n
    case Rn.Leaks{}:
      0n
    case Rn.Loops{}:
      row

# under the cap a retry with the next note of the recovery; at it, cap
def rust.redo(under: Bool, row: Nat, cap: Rn.Help) -> Rn.Help:
  match under:
    case True{}:
      Rn.Redoes{1n+row}
    case False{}:
      cap

# calls below REPEAT_CALLS rounds in a row run; else the other act
def rust.calls(fresh: Bool, other: Rn.Help) -> Rn.Help:
  match fresh:
    case True{}:
      Rn.Runs{}
    case False{}:
      other

# `recover`
def rust.recover(rc: Rn.RCfg, s: Rn.Stuck, +k: Rn.Rk, +row: Nat) -> Rn.Help:
  match rc:
    case Rn.RCfg{long, leak, redirect, repeat}:
      match s:
        case Rn.Truncated{}:
          rust.redo(Nat.is_lt(rust.long_row(k, row), long), rust.long_row(k, row), Rn.Quits{})
        case Rn.Leaked{}:
          rust.redo(Nat.is_lt(rust.leak_row(k, row), leak), rust.leak_row(k, row), Rn.Stands{})
        case Rn.Repeats{before}:
          rust.calls(Nat.is_lt(1n+before, repeat), rust.redo(Nat.is_lt(rust.loop_row(k, row), redirect), rust.loop_row(k, row), Rn.Quits{}))

# LAW: what a recovery does with any stuck reply, after any note, under
# any caps, is what `recover` did: the code that runs is the recoveries
# whose laws are above
law rec_recover_is_the_rust_rule:
  for +rc: Rn.RCfg
  for +s: Rn.Stuck
  for +k: Rn.Rk
  for +row: Nat
  {Rn.decide.recover(rc, s, k, row) == rust.recover(rc, s, k, row) : Rn.Help}

# ---- run_ffi ----

# LAWS (H4.10): the entry of the run's decisions in the compiled core
# (bend/ffi_run.bend). Each law is an open claim; PROOF.bend section
# run_ffi proves them (as Laws.<law>) from the laws of section wire.
# bend/ffi_run.bend: Rust writes a request (the decision's tag and its
# inputs) with eukhe_bend::wire::Writer, and reads the decision's value
# from the answer. Its codec composes the primitives of bend/wire.bend, so
# these laws rest on LAWS.bend section wire.

# Every Nat of a request fits the wire (at most 14 digits: Rust saturates
# its u64 counts at eukhe_bend::wire::NAT_MAX and its u32s fit)
def run.lim_fits(l: Rn.Lim) -> Bool:
  match l:
    case Rn.Lim{rounds, wait, retries, notes}:
      Bool.and(LawsBase.wire_fits(rounds), Bool.and(LawsBase.wire_fits(wait), Bool.and(LawsBase.wire_fits(retries), LawsBase.wire_fits(notes))))

def run.at_fits(t: Rn.At) -> Bool:
  match t:
    case Rn.At{attempt, notes, waited, compacted}:
      Bool.and(LawsBase.wire_fits(attempt), Bool.and(LawsBase.wire_fits(notes), LawsBase.wire_fits(waited)))

def run.rcfg_fits(c: Rn.RCfg) -> Bool:
  match c:
    case Rn.RCfg{long, leak, redirect, repeat}:
      Bool.and(LawsBase.wire_fits(long), Bool.and(LawsBase.wire_fits(leak), Bool.and(LawsBase.wire_fits(redirect), LawsBase.wire_fits(repeat))))

def run.stuck_fits(s: Rn.Stuck) -> Bool:
  match s:
    case Rn.Truncated{}:
      True{}
    case Rn.Leaked{}:
      True{}
    case Rn.Repeats{before}:
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
def run.end_fits(e: Rn.End) -> Bool:
  match e:
    case Rn.EndStop{}:
      True{}
    case Rn.EndReset{}:
      True{}
    case Rn.EndCapped{}:
      True{}
    case Rn.EndNext{count}:
      LawsBase.wire_fits(count)

def run.help_fits(h: Rn.Help) -> Bool:
  match h:
    case Rn.Runs{}:
      True{}
    case Rn.Redoes{row}:
      LawsBase.wire_fits(row)
    case Rn.Stands{}:
      True{}
    case Rn.Quits{}:
      True{}

# LAW: every request whose Nats fit the wire reads back as itself, and its
# reading consumes exactly its encoding
# EXCLUDES: a field read into another, a wrong tag, a lost or eaten rest
law run_ffi_ask_round_trip:
  for +a: FRn.Ask
  for +rest: String
  for +h: {run.ask_fits(a) == True{} : Bool}
  {FRn.get_ask(FRn.put_ask(a, rest)) == Wr.Got{a, rest} : Wr.Dec<FRn.Ask>}

# LAW: witness: a request whose Nats fit the wire exists
law run_ffi_ask_fits_witness:
  exs a: FRn.Ask
  {run.ask_fits(a) == True{} : Bool}

# LAW: the entry answers a request with the value of its decision
# EXCLUDES: an entry that answers another decision, or a default
law run_ffi_answers:
  for +a: FRn.Ask
  for +h: {run.ask_fits(a) == True{} : Bool}
  {FRn.ffi(FRn.put_ask(a, "")) == FRn.answer(a) : String}

# LAW: a request with input left over after it is refused
# EXCLUDES: trailing input read as part of a request, or ignored
law run_ffi_refuses_left_over:
  for +a: FRn.Ask
  for +rest: String
  for +h: {run.ask_fits(a) == True{} : Bool}
  for +more: {String.is_empty(rest) == False{} : Bool}
  {FRn.ffi(FRn.put_ask(a, rest)) == Wr.err("run: input left over after the request") : String}

# LAW: witness: input is left over after a request
law run_ffi_left_over_witness:
  exs rest: String
  {String.is_empty(rest) == False{} : Bool}

# LAW: a malformed request answers the error form, never a decision
# EXCLUDES: a default decision for input the entry cannot read
law run_ffi_refuses_malformed:
  for +s: String
  for +bad: {FRn.get_ask(s) == Wr.Bad{} : Wr.Dec<FRn.Ask>}
  {FRn.ffi(s) == Wr.err("run: malformed request") : String}

# LAW: witness: a malformed request exists
law run_ffi_malformed_witness:
  exs s: String
  {FRn.get_ask(s) == Wr.Bad{} : Wr.Dec<FRn.Ask>}

# LAW: every answer reads back as itself: the step after a reply, what
# preparation does, how a round ends, what a recovery does, the reply a
# message makes (Rust's Reader reads the same grammar)
# EXCLUDES: two answers with one encoding, an answer Rust misreads
law run_ffi_then_round_trip:
  for +x: Rn.Then
  for +rest: String
  {FRn.get_then(FRn.put_then(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.Then>}

law run_ffi_prepared_round_trip:
  for +x: Rn.Prepared
  for +rest: String
  {FRn.get_prepared(FRn.put_prepared(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.Prepared>}

law run_ffi_end_round_trip:
  for +x: Rn.End
  for +rest: String
  for +h: {run.end_fits(x) == True{} : Bool}
  {FRn.get_end(FRn.put_end(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.End>}

law run_ffi_help_round_trip:
  for +x: Rn.Help
  for +rest: String
  for +h: {run.help_fits(x) == True{} : Bool}
  {FRn.get_help(FRn.put_help(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.Help>}

law run_ffi_reply_round_trip:
  for +x: Rn.Reply
  for +rest: String
  {FRn.get_reply(FRn.put_reply(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.Reply>}

# LAW: witness: answers whose Nats fit the wire exist
law run_ffi_answer_fits_witness:
  exs e: Rn.End
  exs x: Rn.Help
  {Bool.and(run.end_fits(e), run.help_fits(x)) == True{} : Bool}
