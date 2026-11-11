# eukhe: the laws of area run: the compiled entry (H4.10)

import Base
import ../../bend/ffi_run.bend as FRn
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/state.bend as RnState
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase

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
    case RnDecision.Thought{window, catalog, prompt, out, cuttable, lower}:
      Bool.and(Bool.and(LawsBase.wire_fits(window), LawsBase.wire_fits(catalog)), Bool.and(LawsBase.wire_fits(prompt), LawsBase.wire_fits(out)))
    case RnDecision.Leaked{}:
      True{}
    case RnDecision.Repeats{before}:
      LawsBase.wire_fits(before)
    case RnDecision.Emptied{}:
      True{}

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
    case RnDecision.Quits{}:
      True{}
    case RnDecision.Compacts{}:
      True{}
    case RnDecision.Lowers{row}:
      LawsBase.wire_fits(row)

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

# The run entry, spelled by the grammar Rust writes and reads
# (crates/eukhe-durable/src/harness/generation/entry.rs `ask`, decide.rs,
# deferred.rs), not by the entry's own encoders: every speller below is
# made of the wire primitives only (bend/wire.bend, laws/wire.bend)

# the limits (`write_limits`): max rounds, the job's ms, max retries, max
# notes
def run_spell_lim(l: RnDecision.Lim, rest: String) -> String:
  match l:
    case RnDecision.Lim{rounds, wait, retries, notes}:
      Wr.put_nat(rounds, Wr.put_nat(wait, Wr.put_nat(retries, Wr.put_nat(notes, rest))))

# the counts of a request: attempt, notes, ms waited, then T when the
# generation compacted
def run_spell_at(t: RnDecision.At, rest: String) -> String:
  match t:
    case RnDecision.At{attempt, notes, waited, compacted}:
      Wr.put_nat(attempt, Wr.put_nat(notes, Wr.put_nat(waited, Wr.put_bool(compacted, rest))))

# a reply: text 0, calls 1, deferred 2, error 3 then retryable and noted,
# overflow 4 then cut
def run_spell_reply(x: RnState.Reply, rest: String) -> String:
  match x:
    case RnState.Plain{}:
      Wr.put_nat(0n, rest)
    case RnState.Calls{}:
      Wr.put_nat(1n, rest)
    case RnState.Deferred{}:
      Wr.put_nat(2n, rest)
    case RnState.Error{retryable, noted}:
      Wr.put_nat(3n, Wr.put_bool(retryable, Wr.put_bool(noted, rest)))
    case RnState.Overflow{cut}:
      Wr.put_nat(4n, Wr.put_bool(cut, rest))

# a message that ends the turn: text, then calls
def run_spell_ended(m: RnState.Ended, rest: String) -> String:
  match m:
    case RnState.Ended{text, calls}:
      Wr.put_bool(text, Wr.put_bool(calls, rest))

# the threshold: none 0, background 1, blocking 2
def run_spell_th(x: RnDecision.Th, rest: String) -> String:
  match x:
    case RnDecision.Under{}:
      Wr.put_nat(0n, rest)
    case RnDecision.Background{}:
      Wr.put_nat(1n, rest)
    case RnDecision.Blocking{}:
      Wr.put_nat(2n, rest)

# how a compaction ended: an entry 0, nothing 1, failed 2
def run_spell_got(x: RnState.Got, rest: String) -> String:
  match x:
    case RnState.Built{}:
      Wr.put_nat(0n, rest)
    case RnState.Kept{}:
      Wr.put_nat(1n, rest)
    case RnState.Broke{}:
      Wr.put_nat(2n, rest)

# the recovery caps: length, leak, redirect, repeat
def run_spell_rcfg(c: RnRecovery.RCfg, rest: String) -> String:
  match c:
    case RnRecovery.RCfg{long, leak, redirect, repeat}:
      Wr.put_nat(long, Wr.put_nat(leak, Wr.put_nat(redirect, Wr.put_nat(repeat, rest))))

# the stuck reply: a length stop 0 then the window, the catalog, the
# prompt, the output, whether it can be cut, whether it can be lowered;
# leak 1, calls 2 then the rounds before, empty 3
def run_spell_stuck(x: RnDecision.Stuck, rest: String) -> String:
  match x:
    case RnDecision.Thought{window, catalog, prompt, out, cuttable, lower}:
      Wr.put_nat(0n, Wr.put_nat(window, Wr.put_nat(catalog, Wr.put_nat(prompt, Wr.put_nat(out, Wr.put_bool(cuttable, Wr.put_bool(lower, rest)))))))
    case RnDecision.Leaked{}:
      Wr.put_nat(1n, rest)
    case RnDecision.Repeats{before}:
      Wr.put_nat(2n, Wr.put_nat(before, rest))
    case RnDecision.Emptied{}:
      Wr.put_nat(3n, rest)

# the recovery of the note: none 0, length 1, leak 2, redirect 3, empty 4
def run_spell_rk(x: RnRecovery.Rk, rest: String) -> String:
  match x:
    case RnRecovery.Free{}:
      Wr.put_nat(0n, rest)
    case RnRecovery.Longs{}:
      Wr.put_nat(1n, rest)
    case RnRecovery.Leaks{}:
      Wr.put_nat(2n, rest)
    case RnRecovery.Loops{}:
      Wr.put_nat(3n, rest)
    case RnRecovery.Empties{}:
      Wr.put_nat(4n, rest)

# a request: the tag of the decision (Rust's `Ask`: reply 0, ended 1,
# prepare 2, compact 3, round 4, recover 5, poll 6), then its inputs
def run_spell_ask(a: FRn.Ask, rest: String) -> String:
  match a:
    case FRn.AskReply{l, t, reply}:
      Wr.put_nat(0n, run_spell_lim(l, run_spell_at(t, run_spell_reply(reply, rest))))
    case FRn.AskEnded{m}:
      Wr.put_nat(1n, run_spell_ended(m, rest))
    case FRn.AskPrepare{compacted, th}:
      Wr.put_nat(2n, Wr.put_bool(compacted, run_spell_th(th, rest)))
    case FRn.AskCompact{over, got}:
      Wr.put_nat(3n, Wr.put_bool(over, run_spell_got(got, rest)))
    case FRn.AskRound{l, count, stops, reset}:
      Wr.put_nat(4n, run_spell_lim(l, Wr.put_nat(count, Wr.put_bool(stops, Wr.put_bool(reset, rest)))))
    case FRn.AskRecover{rc, s, k, row}:
      Wr.put_nat(5n, run_spell_rcfg(rc, run_spell_stuck(s, run_spell_rk(k, Wr.put_nat(row, rest)))))
    case FRn.AskPoll{retryable, failures, retries}:
      Wr.put_nat(6n, Wr.put_bool(retryable, Wr.put_nat(failures, Wr.put_nat(retries, rest))))

# the step after a reply (Rust's `Step`): answer 0, tools 1, poll 2, retry
# 3, note 4, compact 5, fail on the model 6, fail at the deadline 7
def run_spell_then(x: RnDecision.Then, rest: String) -> String:
  match x:
    case RnDecision.DoAnswer{}:
      Wr.put_nat(0n, rest)
    case RnDecision.DoTools{}:
      Wr.put_nat(1n, rest)
    case RnDecision.DoPoll{}:
      Wr.put_nat(2n, rest)
    case RnDecision.DoRetry{}:
      Wr.put_nat(3n, rest)
    case RnDecision.DoNote{}:
      Wr.put_nat(4n, rest)
    case RnDecision.DoCompact{}:
      Wr.put_nat(5n, rest)
    case RnDecision.DoFail{}:
      Wr.put_nat(6n, rest)
    case RnDecision.DoLate{}:
      Wr.put_nat(7n, rest)

# what preparation does (Rust's `Prepared`): wait for a compaction 0, send
# 1 then whether a background compaction starts
def run_spell_prepared(x: RnDecision.Prepared, rest: String) -> String:
  match x:
    case RnDecision.Waits{}:
      Wr.put_nat(0n, rest)
    case RnDecision.Sends{background}:
      Wr.put_nat(1n, Wr.put_bool(background, rest))

# how a round ends (Rust's `RoundEnd`): stop 0, reset 1, capped 2, next 3
# then the rounds
def run_spell_end(x: RnDecision.End, rest: String) -> String:
  match x:
    case RnDecision.EndStop{}:
      Wr.put_nat(0n, rest)
    case RnDecision.EndReset{}:
      Wr.put_nat(1n, rest)
    case RnDecision.EndCapped{}:
      Wr.put_nat(2n, rest)
    case RnDecision.EndNext{count}:
      Wr.put_nat(3n, Wr.put_nat(count, rest))

# what a recovery does (Rust's `Act`): run 0, redo 1 then the row, quit
# 2, compact 3, lower 4 then the row
def run_spell_help(x: RnDecision.Help, rest: String) -> String:
  match x:
    case RnDecision.Runs{}:
      Wr.put_nat(0n, rest)
    case RnDecision.Redoes{row}:
      Wr.put_nat(1n, Wr.put_nat(row, rest))
    case RnDecision.Quits{}:
      Wr.put_nat(2n, rest)
    case RnDecision.Compacts{}:
      Wr.put_nat(3n, rest)
    case RnDecision.Lowers{row}:
      Wr.put_nat(4n, Wr.put_nat(row, rest))

# the spelled answer to request a: the value of its decision in the model
# (bend/run/decision.bend, bend/run/state.bend), which the laws of
# laws/run/model.bend state (run_reply_is_the_rust_rule,
# run_prepare_is_the_rust_rule, run_compact_is_the_rust_rule,
# run_round_is_the_rust_rule, rec_recover_is_the_rust_rule; Ended.reply by
# run_no_answer_is_an_error and run_calls_never_answer, decide.poll by
# run_failed_poll_is_the_job_model) and run_ffi_tags_example anchors
def run_spell_answer(a: FRn.Ask) -> String:
  match a:
    case FRn.AskReply{l, t, reply}:
      run_spell_then(RnDecision.decide.reply(l, t, reply), "")
    case FRn.AskEnded{m}:
      run_spell_reply(RnState.Ended.reply(m), "")
    case FRn.AskPrepare{compacted, th}:
      run_spell_prepared(RnDecision.decide.prepare(compacted, th), "")
    case FRn.AskCompact{over, got}:
      Wr.put_bool(RnDecision.decide.compact(over, got), "")
    case FRn.AskRound{l, count, stops, reset}:
      run_spell_end(RnDecision.decide.round(l, count, stops, reset), "")
    case FRn.AskRecover{rc, s, k, row}:
      run_spell_help(RnDecision.decide.recover(rc, s, k, row), "")
    case FRn.AskPoll{retryable, failures, retries}:
      Wr.put_bool(RnDecision.decide.poll(retryable, failures, retries), "")

# LAW run_ffi_answers_spelled: a request spelled by the grammar Rust writes, every number
# within the wire, is answered with the grammar's spelling of the value of
# its decision in the model
# EXCLUDES: a request or answer tag that drifts from the grammar Rust reads
#   and writes (swapped on both sides of the entry alike), a flag written
#   reversed, a field lost, swapped or defaulted, another decision answered
law run_ffi_answers_spelled:
  for +a: FRn.Ask
  for fits: {run.ask_fits(a) == True{} : Bool}
  {FRn.ffi(run_spell_ask(a, "")) == run_spell_answer(a) : String}

# LAW run_ffi_left_over_spelled: a spelled request that fits, followed by any more input,
# answers the error form "run: input left over after the request"
# EXCLUDES: trailing input ignored, or read as part of the request, or
#   answered with another error text
law run_ffi_left_over_spelled:
  for +a: FRn.Ask
  for fits: {run.ask_fits(a) == True{} : Bool}
  for +c: Char
  for +t: String
  {FRn.ffi(run_spell_ask(a, SCon{c, t})) == Wr.err("run: input left over after the request") : String}

# LAW run_ffi_unknown_ask: a request tag of 7 or more (of any length) answers the error
# form "run: malformed request", whatever follows
# EXCLUDES: an unknown decision read as a known one, or refused with
#   another error text
law run_ffi_unknown_ask:
  for +n: Nat
  for +rest: String
  {FRn.ffi(Wr.put_nat(7n+n, rest)) == Wr.err("run: malformed request") : String}

# LAW run_ffi_reads_only_requests: an answer that is not the error form answers a request:
# the input is exactly the spelling of a request whose numbers fit the
# wire, and the answer is the spelled value of its decision
# EXCLUDES: a decoder that accepts an unknown tag (request, reply,
#   threshold, compaction, stuck reply, recovery), a missing or extra
#   field, or input left over, and answers it anyway (a default instead of
#   the error form)
law run_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FRn.ffi(s)) == False{} : Bool}
  exs a: FRn.Ask
  {(s, (run.ask_fits(a), FRn.ffi(s))) == (run_spell_ask(a, ""), (True{}, run_spell_answer(a))) : String & (Bool & String)}

# LAW run_ffi_malformed_unless_request: every answer but the error form "run: malformed
# request" comes from an input that begins with a spelled request that fits
# EXCLUDES: the left-over error (or any answer) for input that does not
#   begin with a request, the malformed error spelled with another text
law run_ffi_malformed_unless_request:
  for +s: String
  for other: {String.eq(FRn.ffi(s), Wr.err("run: malformed request")) == False{} : Bool}
  exs a: FRn.Ask
  exs rest: String
  {(s, run.ask_fits(a)) == (run_spell_ask(a, rest), True{}) : String & Bool}

# LAW run_ffi_tags_example: anchor: the bytes Rust sends and reads. Limits 2 rounds, 5 ms,
# 1 retry, 1 note; a first attempt, nothing waited, not compacted: text
# answers (0,), calls run tools (1,), deferred polls (2,), a retryable
# error retries (3,), a noted one notes (4,), an overflow with a cut
# compacts (5,), without one fails (6,), deferred at 5 ms is late (7,). A
# message with text and no call is text (0,), with a call calls (1,),
# with neither a noted error (3,FT). Not compacted over a blocking
# threshold waits (0,), over a background one sends with a background
# compaction (1,T); compacted, sends alone (1,F). An overflow's
# compaction goes on after an entry (T), not after nothing (F); a
# threshold one after nothing (T), not after a failure (F). A round after
# 0 of 2 goes on with 1 (3,1,), after 1 is capped (2,), a control stops
# (0,), a reset resets (1,). Caps 2, 2, 2, 5: a length stop with an
# unknown window, no compaction to make and no lower level is redone
# (1,1,), a leak at its cap quits (2,), a first repeat runs (0,), the
# length stop at its cap quits (2,). A retryable failed poll with 0 of 1
# failures repolls (T), with 1 does not (F)
# EXCLUDES: a tag table both sides of the Bend entry agree on but Rust
#   does not, a reversed flag, a field read in another order
law run_ffi_tags_example:
  {[FRn.ffi("0,2,5,1,1,1,0,0,F0,"), FRn.ffi("0,2,5,1,1,1,0,0,F1,"), FRn.ffi("0,2,5,1,1,1,0,0,F2,"), FRn.ffi("0,2,5,1,1,1,0,0,F3,TF"), FRn.ffi("0,2,5,1,1,1,0,0,F3,FT"), FRn.ffi("0,2,5,1,1,1,0,0,F4,T"), FRn.ffi("0,2,5,1,1,1,0,0,F4,F"), FRn.ffi("0,2,5,1,1,1,0,5,F2,"), FRn.ffi("1,TF"), FRn.ffi("1,FT"), FRn.ffi("1,FF"), FRn.ffi("2,F2,"), FRn.ffi("2,F1,"), FRn.ffi("2,T2,"), FRn.ffi("3,T0,"), FRn.ffi("3,T1,"), FRn.ffi("3,F1,"), FRn.ffi("3,F2,"), FRn.ffi("4,2,5,1,1,0,FF"), FRn.ffi("4,2,5,1,1,1,FF"), FRn.ffi("4,2,5,1,1,0,TF"), FRn.ffi("4,2,5,1,1,0,FT"), FRn.ffi("5,2,2,2,5,0,0,0,0,0,FF0,0,"), FRn.ffi("5,2,2,2,5,1,2,2,"), FRn.ffi("5,2,2,2,5,2,0,0,0,"), FRn.ffi("5,2,2,2,5,0,0,0,0,0,FF1,2,"), FRn.ffi("6,T0,1,"), FRn.ffi("6,T1,1,")] == ["0,", "1,", "2,", "3,", "4,", "5,", "6,", "7,", "0,", "1,", "3,FT", "0,", "1,T", "1,F", "T", "F", "T", "F", "3,1,", "2,", "0,", "1,", "1,1,", "2,", "0,", "2,", "T", "F"] : List<&2, String>}

# LAW run_ffi_errors_example: anchor: the error bytes Rust reads: an unknown request (7),
# reply (5), threshold (3), compaction (3), stuck reply (4) or recovery
# (5) tag is malformed, as is no input; a request with input left over is
# refused as such
# EXCLUDES: an unknown tag read as a known one, the two error texts
#   swapped or reworded
law run_ffi_errors_example:
  {[FRn.ffi("7,"), FRn.ffi("0,2,5,1,1,1,0,0,F5,"), FRn.ffi("2,F3,"), FRn.ffi("3,T3,"), FRn.ffi("5,2,2,2,5,4,"), FRn.ffi("5,2,2,2,5,1,5,0,"), FRn.ffi(""), FRn.ffi("6,T0,1,x")] == [Wr.err("run: malformed request"), Wr.err("run: malformed request"), Wr.err("run: malformed request"), Wr.err("run: malformed request"), Wr.err("run: malformed request"), Wr.err("run: malformed request"), Wr.err("run: malformed request"), Wr.err("run: input left over after the request")] : List<&2, String>}
