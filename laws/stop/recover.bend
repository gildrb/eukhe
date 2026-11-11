# eukhe: the laws of area stop, section recover: what the recoveries of
# the Directors' stops do, stated over the entries Rust calls
# (bend/ffi_run.bend: `decide.recover`, decide.rs `recover`, and
# `decide.reply`, decide.rs `after_reply`) and over the recoveries'
# helpers other areas' laws read (bend/run/recovery.bend). R4, R5 (the
# cap of the length notes of a cut reply with text), R7 and R9 are the
# requirements of laws/stop.bend.
#
# The note Rust passes back: `recover` answers Redoes{n} or Lowers{n};
# Rust ends the next request with the note of that row (generation.rs:
# NoteCause::NoAnswer{row} for an empty reply, NoteCause::Length{row}
# for a length stop with no text) and asks `recover` about that request's
# reply with the note's recovery and row (note.rs `NoteCause::recovery`:
# Empty or Length, the row). The laws below feed each help's row back
# that way. The caps come from the requirement: EMPTY_STOP_MAX_RETRIES = 3
# (the 1st to 3rd empty stop get a reminder, the 4th ends the turn; any
# other reply resets the count).

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ../../bend/ffi_run.bend as FRn
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase

# Spec helpers
# ------------

# the note is an empty note (NoteCause::NoAnswer)
def empty_note(k: RnRecovery.Rk) -> Bool:
  match k:
    case RnRecovery.Free{}:
      False{}
    case RnRecovery.Longs{}:
      False{}
    case RnRecovery.Leaks{}:
      False{}
    case RnRecovery.Loops{}:
      False{}
    case RnRecovery.Empties{}:
      True{}

# the note is a length note (NoteCause::Length or Cut)
def length_note(k: RnRecovery.Rk) -> Bool:
  match k:
    case RnRecovery.Free{}:
      False{}
    case RnRecovery.Longs{}:
      True{}
    case RnRecovery.Leaks{}:
      False{}
    case RnRecovery.Loops{}:
      False{}
    case RnRecovery.Empties{}:
      False{}

# the helps a row of stuck replies s gets, the first of them h: each next
# request carries the length note of the row the help before made (a
# Redoes or Lowers row); a help that makes no note (calls, a failure, a
# compaction) ends the row, and so do `fuel` replies
def climb(fuel: Nat, +rc: RnRecovery.RCfg, +s: RnDecision.Stuck, +h: RnDecision.Help) -> List<&2, RnDecision.Help>:
  match fuel:
    case 0n:
      [h]
    case 1n+f:
      match h:
        case RnDecision.Runs{}:
          [RnDecision.Runs{}]
        case RnDecision.Redoes{+n}:
          RnDecision.Redoes{n} <> climb(f, rc, s, RnDecision.decide.recover(rc, s, RnRecovery.Longs{}, n))
        case RnDecision.Quits{}:
          [RnDecision.Quits{}]
        case RnDecision.Compacts{}:
          [RnDecision.Compacts{}]
        case RnDecision.Lowers{+n}:
          RnDecision.Lowers{n} <> climb(f, rc, s, RnDecision.decide.recover(rc, s, RnRecovery.Longs{}, n))

# m notes in a row after j notes (Redoes j+1 to j+m), then tail
def ups(m: Nat, +j: Nat, tail: List<&2, RnDecision.Help>) -> List<&2, RnDecision.Help>:
  match m:
    case 0n:
      tail
    case 1n+q:
      RnDecision.Redoes{1n+j} <> ups(q, 1n+j, tail)

# the end of the ladder after n length notes: one more note one level
# lower when a lower level exists, then the run fails
def ladder_end(lower: Bool, n: Nat) -> List<&2, RnDecision.Help>:
  match lower:
    case True{}:
      [RnDecision.Lowers{1n+n}, RnDecision.Quits{}]
    case False{}:
      [RnDecision.Quits{}]

# Rust's request for the recovery of a cut reply with text after `row`
# length notes in a row (decide.rs `recover`, entry.rs `Ask` tag 5: the
# caps length, leak, redirect, repeat; the stuck reply, 0 a length stop
# with text; the note's recovery, 1 a length note; the row), spelled with
# the wire primitives
def cut_ask(long: Nat, leak: Nat, redirect: Nat, repeat: Nat, row: Nat) -> String:
  Wr.put_nat(5n, Wr.put_nat(long, Wr.put_nat(leak, Wr.put_nat(redirect, Wr.put_nat(repeat, Wr.put_nat(0n, Wr.put_nat(1n, Wr.put_nat(row, ""))))))))

# every Nat of that request fits the wire
def cut_fits(long: Nat, leak: Nat, redirect: Nat, repeat: Nat, row: Nat) -> Bool:
  Bool.and(Bool.and(LawsBase.wire_fits(long), Bool.and(LawsBase.wire_fits(leak), Bool.and(LawsBase.wire_fits(redirect), LawsBase.wire_fits(repeat)))), LawsBase.wire_fits(row))

# the reply is tool calls
def is_calls(q: RnState.Reply) -> Bool:
  match q:
    case RnState.Plain{}:
      False{}
    case RnState.Calls{}:
      True{}
    case RnState.Deferred{}:
      False{}
    case RnState.Error{retryable, noted}:
      False{}
    case RnState.Overflow{cut}:
      False{}

# the reply is a plain one (text, no call): the answer
def is_plain(q: RnState.Reply) -> Bool:
  match q:
    case RnState.Plain{}:
      True{}
    case RnState.Calls{}:
      False{}
    case RnState.Deferred{}:
      False{}
    case RnState.Error{retryable, noted}:
      False{}
    case RnState.Overflow{cut}:
      False{}

# the step after a reply takes it as the run's answer
def is_answer(t: RnDecision.Then) -> Bool:
  match t:
    case RnDecision.DoAnswer{}:
      True{}
    case RnDecision.DoTools{}:
      False{}
    case RnDecision.DoPoll{}:
      False{}
    case RnDecision.DoRetry{}:
      False{}
    case RnDecision.DoNote{}:
      False{}
    case RnDecision.DoCompact{}:
      False{}
    case RnDecision.DoFail{}:
      False{}
    case RnDecision.DoLate{}:
      False{}

# n rounds of the calls of hash h, each with the results of the round
# before
def kept_rounds(n: Nat, +h: Nat) -> List<&2, RnRecovery.Out>:
  match n:
    case 0n:
      []
    case 1n+m:
      RnRecovery.Ran{h, True{}} <> kept_rounds(m, h)

# Laws: an empty reply (R4)
# -------------------------

# LAW stop_empty_three_notes_then_fails (R4): under any caps, after a
# request whose note is no empty note (no note, or a note of another
# recovery, of any row), empty replies, each request carrying the empty
# note the help before made, get empty notes 1, 2 and 3, then the run
# fails (the requirement: three reminders, the fourth empty stop ends the
# turn)
# EXCLUDES: an empty reply nudged forever, a cap off by one either way, a
#   row that does not grow, a row that does not start at 1 after another
#   note, an empty reply that fails the run before its cap
law stop_empty_three_notes_then_fails:
  for +rc: RnRecovery.RCfg
  for +k: RnRecovery.Rk
  for +row: Nat
  for other: {empty_note(k) == False{} : Bool}
  {[RnDecision.decide.recover(rc, RnDecision.Emptied{}, k, row), RnDecision.decide.recover(rc, RnDecision.Emptied{}, RnRecovery.Empties{}, 1n), RnDecision.decide.recover(rc, RnDecision.Emptied{}, RnRecovery.Empties{}, 2n), RnDecision.decide.recover(rc, RnDecision.Emptied{}, RnRecovery.Empties{}, 3n)] == [RnDecision.Redoes{1n}, RnDecision.Redoes{2n}, RnDecision.Redoes{3n}, RnDecision.Quits{}] : List<&2, RnDecision.Help>}

# LAW stop_empty_capped_at_three (R4): after an empty note of row 3 or
# more (any row a stored note may hold), under any caps, an empty reply
# fails the run: there is never a fourth empty note in a row
# EXCLUDES: a cap that holds only at row 3 (a row past it, from a note
#   stored by an older build, nudged again)
law stop_empty_capped_at_three:
  for +rc: RnRecovery.RCfg
  for +x: Nat
  {RnDecision.decide.recover(rc, RnDecision.Emptied{}, RnRecovery.Empties{}, 3n+x) == RnDecision.Quits{} : RnDecision.Help}

# Laws: the length notes of a cut reply with text (R5)
# ----------------------------------------------------

# LAW stop_cut_notes_follow_the_cap (R5): under any caps (`long` length
# notes, any other caps), after a request whose note is no length note
# (any row), cut replies with text, each request carrying the length note
# the help before made, get length notes 1 to `long`, then the run fails
# (the requirement: `Attempt #1/3` to `#3/3`, then the turn ends)
# EXCLUDES: a cap other than the configured one (a fixed cap of 1 or 3
#   that ignores `long`), a row that skips, repeats or does not start at
#   1 after another note, a cut reply that fails the run before its cap
#   or is retried past it
law stop_cut_notes_follow_the_cap:
  for +rc: RnRecovery.RCfg
  for +k: RnRecovery.Rk
  for +row: Nat
  for other: {length_note(k) == False{} : Bool}
  {climb(1n+RnRecovery.RCfg.long(rc), rc, RnDecision.Truncated{}, RnDecision.decide.recover(rc, RnDecision.Truncated{}, k, row)) == ups(RnRecovery.RCfg.long(rc), 0n, [RnDecision.Quits{}]) : List<&2, RnDecision.Help>}

# LAW stop_cut_entry_follows_the_cap (R5, R6): on the wire (the shipped
# entry, bend/ffi_run.bend), Rust's request for a cut reply with text
# after k length notes in a row answers, under a length cap past k (k + 1
# + x, any x, any other caps), a retry with length note k + 1 (`1,<k+1>,`),
# and under a length cap of k the failure (`2,`); every Nat of both
# requests within the wire
# EXCLUDES: an entry that answers a fixed cap, misreads the cap, the row
#   or the reply's kind, or answers another note than the next
law stop_cut_entry_follows_the_cap:
  for +k: Nat
  for +x: Nat
  for +le: Nat
  for +re: Nat
  for +rp: Nat
  for fa: {cut_fits(1n+Nat.add(x, k), le, re, rp, k) == True{} : Bool}
  for fb: {cut_fits(k, le, re, rp, k) == True{} : Bool}
  {[FRn.ffi(cut_ask(1n+Nat.add(x, k), le, re, rp, k)), FRn.ffi(cut_ask(k, le, re, rp, k))] == [Wr.put_nat(1n, Wr.put_nat(1n+k, "")), Wr.put_nat(2n, "")] : List<&2, String>}

# Laws: a length stop with no text (R7)
# -------------------------------------

# LAW stop_think_ladder_climbs (R7): under any caps (`long` length notes),
# with no compaction to run (cuttable false; any window, catalog cap,
# prompt and output), after a request whose note is no length note (any
# row), length stops with no text, each request carrying the length note
# the help before made, get length notes 1 to `long`, then, when a level
# below the agent's exists, note long + 1 one level lower, then the run
# fails
# EXCLUDES: a ladder that skips or repeats a note, fails the run before
#   its last rung, lowers the level before the notes run out or more than
#   once, never fails the run, or does not start at note 1 after another
#   note
law stop_think_ladder_climbs:
  for +rc: RnRecovery.RCfg
  for +w: Nat
  for +c: Nat
  for +p: Nat
  for +o: Nat
  for +lower: Bool
  for +k: RnRecovery.Rk
  for +row: Nat
  for other: {length_note(k) == False{} : Bool}
  {climb(1n+RnRecovery.RCfg.long(rc), rc, RnDecision.Thought{w, c, p, o, False{}, lower}, RnDecision.decide.recover(rc, RnDecision.Thought{w, c, p, o, False{}, lower}, k, row)) == ups(RnRecovery.RCfg.long(rc), 0n, ladder_end(lower, RnRecovery.RCfg.long(rc))) : List<&2, RnDecision.Help>}

# LAW stop_think_compacts_when_window_ran_out (R7, spec S7): a length stop
# with no text whose window ran out (the window is known, the output is
# below the model's catalog max output, and prompt + output + 8192 tokens
# reach the window; 8192: twice CONTEXT_SAFETY_TOKENS 4096 of eukhe-ai
# simple_options.rs, the error of the prompt's estimate) and that can
# compact compacts, after any note of any row, under any caps
# EXCLUDES: a retry at the same output cap while the window is what ran
#   out (the 3 identical retries of v0.10.59), a margin smaller than the
#   requirement's
law stop_think_compacts_when_window_ran_out:
  for +rc: RnRecovery.RCfg
  for +w: Nat
  for +c: Nat
  for +p: Nat
  for +o: Nat
  for +lower: Bool
  for +k: RnRecovery.Rk
  for +row: Nat
  for below: {Nat.is_lt(o, c) == True{} : Bool}
  for reach: {Nat.is_le(1n+w, Nat.add(Nat.add(p, o), 8192n)) == True{} : Bool}
  {RnDecision.decide.recover(rc, RnDecision.Thought{1n+w, c, p, o, True{}, lower}, k, row) == RnDecision.Compacts{} : RnDecision.Help}

# LAW stop_think_unknown_window_or_catalog_cut (R7, spec S7): with the
# window unknown (0), or the output at or past the catalog max output
# (the catalog cap, not the window, stopped the reply), a length stop with
# no text that could compact gets what it gets with no compaction to run
# (stop_think_ladder_climbs), after any note, under any caps
# EXCLUDES: a compaction when the window is unknown, or when the catalog
#   cap stopped the reply
law stop_think_unknown_window_or_catalog_cut:
  for +rc: RnRecovery.RCfg
  for +w: Nat
  for +c: Nat
  for +p: Nat
  for +o: Nat
  for +x: Nat
  for +lower: Bool
  for +k: RnRecovery.Rk
  for +row: Nat
  {RnDecision.decide.recover(rc, RnDecision.Thought{0n, c, p, o, True{}, lower}, k, row) == RnDecision.decide.recover(rc, RnDecision.Thought{0n, c, p, o, False{}, lower}, k, row) : RnDecision.Help} &
  {RnDecision.decide.recover(rc, RnDecision.Thought{w, c, p, Nat.add(c, x), True{}, lower}, k, row) == RnDecision.decide.recover(rc, RnDecision.Thought{w, c, p, Nat.add(c, x), False{}, lower}, k, row) : RnDecision.Help}

# LAW stop_think_room_left_never_compacts (R7, spec S7): when prompt +
# output + 8192 tokens stay below the window, a length stop with no text
# that could compact gets what it gets with no compaction to run, after
# any note, under any caps
# EXCLUDES: a compaction while the window still had room (the output cap
#   stopped the reply: compacting would not help)
law stop_think_room_left_never_compacts:
  for +rc: RnRecovery.RCfg
  for +w: Nat
  for +c: Nat
  for +p: Nat
  for +o: Nat
  for +lower: Bool
  for +k: RnRecovery.Rk
  for +row: Nat
  for room: {Nat.is_lt(Nat.add(Nat.add(p, o), 8192n), w) == True{} : Bool}
  {RnDecision.decide.recover(rc, RnDecision.Thought{w, c, p, o, True{}, lower}, k, row) == RnDecision.decide.recover(rc, RnDecision.Thought{w, c, p, o, False{}, lower}, k, row) : RnDecision.Help}

# LAW stop_shrink_once_a_generation (R7): the compaction rung's reply,
# under any limits, at any attempt and notes of a generation, compacts
# when the generation has not compacted and fails the run when it has:
# at most one compaction a generation
# EXCLUDES: a second compaction in a generation (a compaction loop), a
#   first one refused
law stop_shrink_once_a_generation:
  for +l: RnDecision.Lim
  for +at: Nat
  for +notes: Nat
  for +waited: Nat
  for -pass: RnState.Reply
  {RnDecision.decide.reply(l, RnDecision.At{at, notes, waited, False{}}, RnRecovery.Act.reply(RnRecovery.Shrink{}, pass)) == RnDecision.DoCompact{} : RnDecision.Then} &
  {RnDecision.decide.reply(l, RnDecision.At{at, notes, waited, True{}}, RnRecovery.Act.reply(RnRecovery.Shrink{}, pass)) == RnDecision.DoFail{} : RnDecision.Then}

# Laws: the recoveries' helpers other laws read (R9)
# -------------------------------------------------

# LAW stop_act_runs_only_calls (R9): an act runs tool calls (Act.runs of
# bend/run/recovery.bend) exactly when the reply it makes of a plain reply
# is the calls
# EXCLUDES: an Act.runs that is never True or always True, a retry, a
#   failure or a compaction read as calls
law stop_act_runs_only_calls:
  for a: RnRecovery.Act
  {RnRecovery.Act.runs(a) == is_calls(RnRecovery.Act.reply(a, RnState.Plain{})) : Bool}

# LAW stop_act_only_pass_keeps (R9): Pass keeps every reply as it was, and
# an act helps (Act.helps, the test rec_stuck_gets_help reads) exactly
# when it does not keep a plain reply plain
# EXCLUDES: an Act.helps that is always True (rec_stuck_gets_help then
#   holds vacuously), a Pass counted as help, a passed reply changed
law stop_act_only_pass_keeps:
  for a: RnRecovery.Act
  for +q: RnState.Reply
  {RnRecovery.Act.helps(a) == Bool.not(is_plain(RnRecovery.Act.reply(a, RnState.Plain{}))) : Bool} &
  {RnRecovery.Act.reply(RnRecovery.Pass{}, q) == q : RnState.Reply}

# LAW stop_act_never_answers (R9): the reply of an act that helps, whatever
# the reply was, is never the run's answer: under any limits, at any
# attempt, notes and compactions of a generation, the step after it
# (decide.reply) is no answer
# EXCLUDES: a recovery that turns a stuck reply into the answer (a cut,
#   empty or markup reply answered after a Director continued it)
law stop_act_never_answers:
  for a: RnRecovery.Act
  for +q: RnState.Reply
  for +l: RnDecision.Lim
  for +t: RnDecision.At
  for helps: {RnRecovery.Act.helps(a) == True{} : Bool}
  {is_answer(RnDecision.decide.reply(l, t, RnRecovery.Act.reply(a, q))) == False{} : Bool}

# LAW stop_capped_past_the_cap (R9): under any caps, a row past its cap is
# not capped (Rk.capped, the test rec_notes_capped reads): past long + 1
# length notes (the lower rung is one more), `leak` leak notes,
# `redirect` redirect notes, 3 empty notes
# EXCLUDES: a cap test that bounds nothing (rec_notes_capped then holds
#   vacuously), a bound off by one upwards, another recovery's cap read
law stop_capped_past_the_cap:
  for +rc: RnRecovery.RCfg
  for +x: Nat
  {RnRecovery.Rk.capped(rc, RnRecovery.Longs{}, Nat.add(2n+RnRecovery.RCfg.long(rc), x)) == False{} : Bool} &
  {RnRecovery.Rk.capped(rc, RnRecovery.Leaks{}, Nat.add(1n+RnRecovery.RCfg.leak(rc), x)) == False{} : Bool} &
  {RnRecovery.Rk.capped(rc, RnRecovery.Loops{}, Nat.add(1n+RnRecovery.RCfg.redirect(rc), x)) == False{} : Bool} &
  {RnRecovery.Rk.capped(rc, RnRecovery.Empties{}, 4n+x) == False{} : Bool}

# LAW stop_repeat_row_counts (R9): a run whose replies are n rounds of
# the same calls with the same results, n below the repeat cap, ran them
# all and counts n rounds in a row (from a run start, which counts none)
# EXCLUDES: a row that never grows (repeats run forever:
#   rec_never_runs_a_repeat then holds vacuously), a row that grows by more
#   than one a round, a run that starts with a round counted
law stop_repeat_row_counts:
  for +rc: RnRecovery.RCfg
  for +h: Nat
  for +n: Nat
  for fresh: {Nat.is_lt(n, RnRecovery.RCfg.repeat(rc)) == True{} : Bool}
  {RnRecovery.Rec.same(RnRecovery.Rec.run(rc, kept_rounds(n, h))) == n : Nat}

# LAW stop_repeat_row_restarts (R9): under a repeat cap past 1, calls of
# another hash than the last round's, after any note and any row, run
# and start a new row of 1
# EXCLUDES: a row that goes on across calls of another hash (different
#   calls redirected as a repeat)
law stop_repeat_row_restarts:
  for +rc: RnRecovery.RCfg
  for +h: Nat
  for +h2: Nat
  for +kept: Bool
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for two: {Nat.is_lt(1n, RnRecovery.RCfg.repeat(rc)) == True{} : Bool}
  for other: {Nat.is_eq(h, h2) == False{} : Bool}
  {RnRecovery.Dec.act(RnRecovery.Rec.step(rc, RnRecovery.Ran{h2, kept}, RnRecovery.Rec{k, row, same, h})) == RnRecovery.Exec{} : RnRecovery.Act} &
  {RnRecovery.Rec.same(RnRecovery.Dec.r(RnRecovery.Rec.step(rc, RnRecovery.Ran{h2, kept}, RnRecovery.Rec{k, row, same, h}))) == 1n : Nat}
