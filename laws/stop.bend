# eukhe: the laws of area stop

import Base
import ../bend/stop.bend as S
import ../bend/ffi_stop.bend as FS
import ../bend/run/state.bend as RnState
import ../bend/run/step.bend as RnStep
import ../bend/run/recovery.bend as RnRecovery
import ../bend/run/decision.bend as RnDecision
import ../bend/run/request.bend as RnRequest
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ../spec/harness/stop.bend as StSpec

# (ST) The Directors at a candidate stop
# --------------------------------------
# bend/stop.bend, run as the compiled core by bend/ffi_stop.bend (asked by
# eukhe-durable harness/generation/stop.rs at every reply that ends the
# model's turn with no tool call), and the caps of its Directors in
# bend/run/recovery.bend (asked through decide.rs `recover`). Every input
# is free: any facts, any window, any round count.
#
# R1: the walk is the spec's (spec/harness/stop.bend S1-S3): LengthStop,
#     EmptyStop, MarkupStop, PendingWork, inside to outside; the first
#     that does not pass decides. A whole, readable reply stands,
#     whatever it says: its text is no fact of the walk, and a reply that
#     was not cut reads no fact of the window.
# R2: each Director's verdict is the spec's (S2): Continue, Pass, Yield or
#     Drop exactly.
# R3: a stop never continues while the session owns running work: it
#     stands (PendingWork never continues).
# R4: the caps (S4): an empty reply is retried with a note at most 3
#     times in a row, then the run fails.
# R5: the round note is the spec's text (S6).
# R6: the entry answers each request Rust writes (0 the walk: cut, text,
#     broken, pending, then the window's facts at a cut reply: window,
#     catalog, prompt, out, cuttable; 1 the round note: max, done; every
#     Nat within the wire) with the spelled spec answer: the pick (0
#     stands, 1-4 the Director, inside to outside, 5 dropped) or the round
#     note (0, none | 1, then the text); reads exactly the request;
#     answers a tag past 1 and input left over with `E stop: malformed
#     request`.
# R7: a length stop that LengthStop continues (no text: the model still
#     reasoned; or full, R10) climbs the spec's ladder (S7), never failing
#     the run while a rung remains: compact when the window ran out and a
#     compaction can run (the row stays); else a length note under the
#     cap; else, once, a length note with the request one thinking level
#     lower (the lower level rides that one noted retry: the note's
#     request only); else the run fails. Each rung is a noted retry or
#     the overflow's compaction, so every run still ends (run_ends: notes
#     and compactions are bounded).
# R8: the reply the run reads at a stop (generation.rs `after_reply`): a
#     stop the walk lets stand with text answers the run once and for
#     good; the run sends no further request and counts one answer,
#     whatever follows. A stop the walk does not let stand never answers
#     the run: its reply is a noted retry, a failure or the overflow's
#     compaction. A dropped stop ends the run as an answer does (R10).
# R9: the recoveries' own helpers that the laws above read are the
#     spec's: only Exec runs calls; every act but Pass helps; the reply
#     each act makes (Pass the reply as it was, Exec the calls, Redo and
#     Lower a noted error, Quit a failure, Shrink a cut overflow); a run
#     starts with no note and no round; each row is within its cap (the
#     length notes one past theirs, Free none); the rounds in a row are one
#     more after a round of the same calls, else 1.
# R10: a reply cut at the output limit, as omp treats it (omp at c28b3e3,
#     packages/coding-agent/src/session/session-maintenance.ts:3399-3534).
#     With no text it never stands. With text it stands exactly when the
#     window has room (S5: not spent; an unknown window is spent, as omp
#     counts it: :3412-3415): the truncated reply is kept as the run's
#     answer, whatever else its text holds; it answers the run once and
#     the run sends no further request. With text and a spent window, the
#     run compacts (the overflow's compaction) when a compaction can run,
#     then the request goes again; when none can, the reply is dropped
#     (:3528-3533): the run ends with no further request, the reply stays
#     in the transcript but leaves the model's context, and no warning
#     follows it (Rust: generation/round.rs `answer`). Its laws:
#     laws/stop/cut.bend.

# Spec helpers
# ------------

# the pick is PendingWork's (it never is: R3)
def pends(p: S.Pick) -> Bool:
  match p:
    case S.Stands{}:
      False{}
    case S.Goes{d}:
      match d:
        case S.LengthStop{}:
          False{}
        case S.EmptyStop{}:
          False{}
        case S.MarkupStop{}:
          False{}
        case S.PendingWork{}:
          True{}
    case S.Drops{}:
      False{}

# the empty notes in a row that a note of recovery k with row `row` makes
# (decide.rs `recover` over `NoteCause::row`)
def rust_empty_row(k: RnRecovery.Rk, row: Nat) -> Nat:
  match k:
    case RnRecovery.Free{}:
      0n
    case RnRecovery.Longs{}:
      0n
    case RnRecovery.Leaks{}:
      0n
    case RnRecovery.Loops{}:
      0n
    case RnRecovery.Empties{}:
      row

def rust_empty.at(under: Bool, row: Nat) -> RnDecision.Help:
  match under:
    case True{}:
      RnDecision.Redoes{1n+row}
    case False{}:
      RnDecision.Quits{}

# R4: what `recover` does with an empty reply, after the request whose
# note counts row notes of the recovery k
def rust_empty(+k: RnRecovery.Rk, +row: Nat) -> RnDecision.Help:
  rust_empty.at(Nat.is_lt(rust_empty_row(k, row), StSpec.empty_cap()), rust_empty_row(k, row))

# the length notes in a row that a note of recovery k with row `row`
# makes (decide.rs `recover` over `NoteCause::row`)
def rust_long_row(k: RnRecovery.Rk, row: Nat) -> Nat:
  match k:
    case RnRecovery.Free{}:
      0n
    case RnRecovery.Longs{}:
      row
    case RnRecovery.Leaks{}:
      0n
    case RnRecovery.Loops{}:
      0n
    case RnRecovery.Empties{}:
      0n

# R7: what `recover` does with a length stop that LengthStop continues,
# the cap of length notes `long`, after the request whose note counts row
# notes of the recovery k
def rust_think(+long: Nat, +k: RnRecovery.Rk, +row: Nat, +window: Nat, +catalog: Nat, +prompt: Nat, +out: Nat, cuttable: Bool, lower: Bool) -> RnDecision.Help:
  StSpec.ladder(StSpec.full(window, catalog, prompt, out, cuttable), lower, rust_long_row(k, row), long)

# the act ends the run
def quits(a: RnRecovery.Act) -> Bool:
  match a:
    case RnRecovery.Pass{}:
      False{}
    case RnRecovery.Exec{}:
      False{}
    case RnRecovery.Redo{}:
      False{}
    case RnRecovery.Quit{}:
      True{}
    case RnRecovery.Shrink{}:
      False{}
    case RnRecovery.Lower{}:
      False{}

# R9: only Exec runs tool calls
def spec_runs(a: RnRecovery.Act) -> Bool:
  match a:
    case RnRecovery.Pass{}:
      False{}
    case RnRecovery.Exec{}:
      True{}
    case RnRecovery.Redo{}:
      False{}
    case RnRecovery.Quit{}:
      False{}
    case RnRecovery.Shrink{}:
      False{}
    case RnRecovery.Lower{}:
      False{}

# R9: every act but Pass does something about the reply
def spec_helps(a: RnRecovery.Act) -> Bool:
  match a:
    case RnRecovery.Pass{}:
      False{}
    case RnRecovery.Exec{}:
      True{}
    case RnRecovery.Redo{}:
      True{}
    case RnRecovery.Quit{}:
      True{}
    case RnRecovery.Shrink{}:
      True{}
    case RnRecovery.Lower{}:
      True{}

# R9: the reply the run's steps read after the act; pass: the reply as
# it was
def spec_act_reply(a: RnRecovery.Act, pass: RnState.Reply) -> RnState.Reply:
  match a:
    case RnRecovery.Pass{}:
      pass
    case RnRecovery.Exec{}:
      RnState.Calls{}
    case RnRecovery.Redo{}:
      RnState.Error{False{}, True{}}
    case RnRecovery.Quit{}:
      RnState.Error{False{}, False{}}
    case RnRecovery.Shrink{}:
      RnState.Overflow{True{}}
    case RnRecovery.Lower{}:
      RnState.Error{False{}, True{}}

# R9: the row of the next note is within its recovery's cap: none for
# Free (no note), one past `long` for length notes (the lower rung)
def spec_capped(+rc: RnRecovery.RCfg, k: RnRecovery.Rk, +row: Nat) -> Bool:
  match rc:
    case RnRecovery.RCfg{long, leak, redirect, repeat}:
      match k:
        case RnRecovery.Free{}:
          True{}
        case RnRecovery.Longs{}:
          Nat.is_lt(row, 2n+long)
        case RnRecovery.Leaks{}:
          Nat.is_lt(row, 1n+leak)
        case RnRecovery.Loops{}:
          Nat.is_lt(row, 1n+redirect)
        case RnRecovery.Empties{}:
          Nat.is_lt(row, 1n+StSpec.empty_cap())

def spec_again.at(more: Bool, same: Nat) -> Nat:
  match more:
    case True{}:
      1n+same
    case False{}:
      1n

# R9: the rounds in a row with hash h after a round: one more than
# `same` when there was a round (same > 0) and its hash `last` is h,
# else a new row of 1
def spec_again(+same: Nat, +last: Nat, +h: Nat) -> Nat:
  spec_again.at(Bool.and(Nat.is_lt(0n, same), Nat.is_eq(last, h)), same)

# R6: the spelling of a request and of its answer
def sp_w_ask(a: FS.Ask, rest: String) -> String:
  match a:
    case FS.AskWalk{c, t, b, p, w, ca, pr, o, cu}:
      Wr.put_nat(0n, Wr.put_bool(c, Wr.put_bool(t, Wr.put_bool(b, Wr.put_bool(p, Wr.put_nat(w, Wr.put_nat(ca, Wr.put_nat(pr, Wr.put_nat(o, Wr.put_bool(cu, rest))))))))))
    case FS.AskRounds{m, d}:
      Wr.put_nat(1n, Wr.put_nat(m, Wr.put_nat(d, rest)))

def sp_w_pick(p: S.Pick) -> String:
  match p:
    case S.Stands{}:
      Wr.put_nat(0n, "")
    case S.Goes{d}:
      match d:
        case S.LengthStop{}:
          Wr.put_nat(1n, "")
        case S.EmptyStop{}:
          Wr.put_nat(2n, "")
        case S.MarkupStop{}:
          Wr.put_nat(3n, "")
        case S.PendingWork{}:
          Wr.put_nat(4n, "")
    case S.Drops{}:
      Wr.put_nat(5n, "")

def sp_w_round(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{t}:
      Wr.put_nat(1n, Wr.put_str(t, ""))

def sp_w_reply(a: FS.Ask) -> String:
  match a:
    case FS.AskWalk{c, t, b, p, +w, +ca, +pr, +o, cu}:
      sp_w_pick(StSpec.pick(StSpec.facts(c, t, b, p, w, ca, pr, o, cu)))
    case FS.AskRounds{m, d}:
      sp_w_round(StSpec.rounds(m, d))

# every Nat and length of the request fits the wire
def sp_fit(a: FS.Ask) -> Bool:
  match a:
    case FS.AskWalk{c, t, b, p, w, ca, pr, o, cu}:
      Bool.and(Bool.and(LawsBase.wire_fits(w), LawsBase.wire_fits(ca)), Bool.and(LawsBase.wire_fits(pr), LawsBase.wire_fits(o)))
    case FS.AskRounds{m, d}:
      Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(d))

# R8: the reply a recovery's help makes the run read (generation.rs, the
# match on `recover`'s Act): a retry with a note, a failure, and for a
# length stop that LengthStop continues (thought) the overflow's
# compaction or a retry one level lower; any other help leaves the reply
# as Ended.reply made it (pass)
def help_reply(h: RnDecision.Help, thought: Bool, pass: RnState.Reply) -> RnState.Reply:
  match h:
    case RnDecision.Runs{}:
      pass
    case RnDecision.Redoes{row}:
      RnState.Error{False{}, True{}}
    case RnDecision.Quits{}:
      RnState.Error{False{}, False{}}
    case RnDecision.Compacts{}:
      match thought:
        case True{}:
          RnState.Overflow{True{}}
        case False{}:
          pass
    case RnDecision.Lowers{row}:
      match thought:
        case True{}:
          RnState.Error{False{}, True{}}
        case False{}:
          pass

# R8: the reply the run reads when the Director d continues it: the help
# of `recover` for the Stuck Rust asks it about (generation.rs: LengthStop
# Thought, with its ladder's facts w, ca, pr, o, cu, lo; EmptyStop Empty;
# MarkupStop Leak), after the request whose note counts row notes of the
# recovery k. PendingWork never continues (R3); Rust takes such a pick
# for an inconsistent build and stops (`expect_core`): a failure
def go_reply(d: S.Dir, +rc: RnRecovery.RCfg, +k: RnRecovery.Rk, +row: Nat, +w: Nat, +ca: Nat, +pr: Nat, +o: Nat, cu: Bool, lo: Bool, pass: RnState.Reply) -> RnState.Reply:
  match d:
    case S.LengthStop{}:
      help_reply(RnDecision.decide.recover(rc, RnDecision.Thought{w, ca, pr, o, cu, lo}, k, row), True{}, pass)
    case S.EmptyStop{}:
      help_reply(RnDecision.decide.recover(rc, RnDecision.Emptied{}, k, row), False{}, pass)
    case S.MarkupStop{}:
      help_reply(RnDecision.decide.recover(rc, RnDecision.Leaked{}, k, row), False{}, pass)
    case S.PendingWork{}:
      RnState.Error{False{}, False{}}

# R8: the reply the run reads at a candidate stop (a reply with no tool
# call; generation.rs `after_reply`) of facts f, the walk's pick p: a
# stop that stands reads the reply as Ended.reply made it (no note, no
# cause), a Director that goes reads its recovery's; a dropped stop reads
# the reply as Ended.reply made it too: the run ends as at an answer
# (Rust takes the reply out of the model's context, R10)
def stop_reply(p: S.Pick, +f: S.Facts, +rc: RnRecovery.RCfg, +k: RnRecovery.Rk, +row: Nat, +w: Nat, +ca: Nat, +pr: Nat, +o: Nat, cu: Bool, lo: Bool) -> RnState.Reply:
  match p:
    case S.Stands{}:
      RnState.Ended.reply(RnState.Ended{S.Facts.text(f), False{}})
    case S.Goes{d}:
      go_reply(d, rc, k, row, w, ca, pr, o, cu, lo, RnState.Ended.reply(RnState.Ended{S.Facts.text(f), False{}}))
    case S.Drops{}:
      RnState.Ended.reply(RnState.Ended{S.Facts.text(f), False{}})

# R8: the reply never answers the run: a retry (noted or not), a failure,
# the overflow's compaction
def retried(q: RnState.Reply) -> Bool:
  match q:
    case RnState.Plain{}:
      False{}
    case RnState.Calls{}:
      False{}
    case RnState.Deferred{}:
      False{}
    case RnState.Error{retryable, noted}:
      True{}
    case RnState.Overflow{cut}:
      True{}

# R8: the phase is the run's answer
def answered(ph: RnState.Ph) -> Bool:
  match ph:
    case RnState.Prepare{}:
      False{}
    case RnState.Call{}:
      False{}
    case RnState.Compact{over}:
      False{}
    case RnState.Tools{}:
      False{}
    case RnState.Answered{}:
      True{}
    case RnState.Aborted{}:
      False{}
    case RnState.Failed{why}:
      False{}

# R8: the answers the phase pa counts: one for the answer phase
def answer.to(pa: RnState.Ph) -> Nat:
  match pa:
    case RnState.Prepare{}:
      0n
    case RnState.Call{}:
      0n
    case RnState.Compact{over}:
      0n
    case RnState.Tools{}:
      0n
    case RnState.Answered{}:
      1n
    case RnState.Aborted{}:
      0n
    case RnState.Failed{why}:
      0n

# R8: an input that takes a live run from phase pb to the answer phase pa
# counts one answer; an ended run counts none
def answer.at(pb: RnState.Ph, pa: RnState.Ph) -> Nat:
  match pb:
    case RnState.Prepare{}:
      answer.to(pa)
    case RnState.Call{}:
      answer.to(pa)
    case RnState.Compact{over}:
      answer.to(pa)
    case RnState.Tools{}:
      answer.to(pa)
    case RnState.Answered{}:
      0n
    case RnState.Aborted{}:
      0n
    case RnState.Failed{why}:
      0n

# R8: the answers a run from s counts over the inputs evs
def answers.go(evs: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +s: RnState.St) -> Nat:
  match evs:
    case Nil{}:
      0n
    case e <> rest:
      +s2 = RnStep.step(cfg, s, e)
      Nat.add(answer.at(RnState.St.ph(s), RnState.St.ph(s2)), answers.go(rest, cfg, s2))

# Laws: the walk (R1-R3)
# ----------------------

# LAW stop_walk_refines (R1): the walk at every stop is the spec's
# EXCLUDES: a Director dropped, added or moved in the stack, a verdict
#   read as another
law stop_walk_refines:
  for +f: S.Facts
  {S.walk(f) == StSpec.pick(f) : S.Pick}

# LAW stop_verdict_exact (R2): every Director's verdict at every stop is
# the spec's: Continue, Pass, Yield or Drop exactly
# EXCLUDES: a Director that yields where it should continue (or the
#   reverse), one that reads another fact
law stop_verdict_exact:
  for +d: S.Dir
  for +f: S.Facts
  {S.verdict(d, f) == StSpec.verdict(d, f) : S.Verdict}

# LAW stop_empty_continues (R1): a whole reply with no text (a
# thinking-only one) never stands: EmptyStop continues it, work pending
# or not, whatever the window
# EXCLUDES: an empty reply read as an answer, or as a pause
law stop_empty_continues:
  for b: Bool
  for p: Bool
  for sp: Bool
  for cu: Bool
  {S.walk(S.Facts{False{}, False{}, b, p, sp, cu}) == S.Goes{S.EmptyStop{}} : S.Pick}

# LAW stop_markup_continues (R1): a whole reply with markup the harness
# could not read never stands: MarkupStop continues it, whatever the
# window
# EXCLUDES: tool-call markup taken as the final answer
law stop_markup_continues:
  for p: Bool
  for sp: Bool
  for cu: Bool
  {S.walk(S.Facts{False{}, True{}, True{}, p, sp, cu}) == S.Goes{S.MarkupStop{}} : S.Pick}

# LAW stop_pending_pauses (R3): a whole, readable reply while the session
# owns running work stands: the stop is a pause, whatever it says and
# whatever the window
# EXCLUDES: a reminder while a job or a child will wake the session
law stop_pending_pauses:
  for sp: Bool
  for cu: Bool
  {S.walk(S.Facts{False{}, True{}, False{}, True{}, sp, cu}) == S.Stands{} : S.Pick}

# LAW stop_reply_stands (R1): a whole, readable reply with no work
# pending stands, whatever it says (a hand-off to the user such as
# 'Next: say "ship it" and I will commit, push and deploy the change.'
# too: the walk reads no text) and whatever the window, on the wire too
# (Rust writes no window for a reply that was not cut: 0s and F, a window
# the walk reads as spent with no compaction to make)
# EXCLUDES: a reminder after a final answer that names a next step, a
#   Director that reads the reply's text, a whole reply continued or
#   dropped because the window is spent
law stop_reply_stands:
  for sp: Bool
  for cu: Bool
  {S.walk(S.Facts{False{}, True{}, False{}, False{}, sp, cu}) == S.Stands{} : S.Pick} &
  {FS.ffi("0,FTFF0,0,0,0,F") == "0," : String}

# LAW stop_pending_never_continues (R3): PendingWork never continues a run
# EXCLUDES: a pause turned into a reminder
law stop_pending_never_continues:
  for +f: S.Facts
  {pends(S.walk(f)) == False{} : Bool}

# LAW stop_walk_example (R1, R3, R10): anchor: a final answer alone and
# with a job running, an empty reply with a job running, a cut reply with
# text and room (kept), a cut reply with text at a spent window with a
# compaction to make (LengthStop) and with none (dropped), a cut reply
# with no text, markup
# EXCLUDES: a walk that drifts from the Directors' order
law stop_walk_example:
  {[S.walk(S.Facts{False{}, True{}, False{}, False{}, False{}, False{}}), S.walk(S.Facts{False{}, True{}, False{}, True{}, False{}, False{}}), S.walk(S.Facts{False{}, False{}, False{}, True{}, False{}, False{}}), S.walk(S.Facts{True{}, True{}, False{}, False{}, False{}, True{}}), S.walk(S.Facts{True{}, True{}, False{}, False{}, True{}, True{}}), S.walk(S.Facts{True{}, True{}, False{}, False{}, True{}, False{}}), S.walk(S.Facts{True{}, False{}, False{}, False{}, False{}, False{}}), S.walk(S.Facts{False{}, True{}, True{}, False{}, False{}, False{}})] == [S.Stands{}, S.Stands{}, S.Goes{S.EmptyStop{}}, S.Stands{}, S.Goes{S.LengthStop{}}, S.Drops{}, S.Goes{S.LengthStop{}}, S.Goes{S.MarkupStop{}}] : List<&2, S.Pick>}

# Laws: the caps (R4)
# -------------------

# LAW stop_empty_redoes (R4): an empty reply under the cap is retried
# with the next empty note
# EXCLUDES: an empty reply that ends the run before its cap, a row that
#   does not count
law stop_empty_redoes:
  for +rc: RnRecovery.RCfg
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for under: {RnRecovery.below(RnRecovery.Rk.empties(k, row), StSpec.empty_cap()) == True{} : Bool}
  {RnRecovery.Rec.step(rc, RnRecovery.Empty{}, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Empties{}, 1n+RnRecovery.Rk.empties(k, row), same, last}} : RnRecovery.Dec}

# LAW stop_empty_gives_up (R4): after 3 empty notes in a row, an empty
# reply fails the run
# EXCLUDES: an endless row of empty replies, an empty reply taken as the
#   answer at the cap
law stop_empty_gives_up:
  for +rc: RnRecovery.RCfg
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for over: {RnRecovery.below(RnRecovery.Rk.empties(k, row), StSpec.empty_cap()) == False{} : Bool}
  {RnRecovery.Dec.act(RnRecovery.Rec.step(rc, RnRecovery.Empty{}, RnRecovery.Rec{k, row, same, last})) == RnRecovery.Quit{} : RnRecovery.Act}

# LAW stop_empty_row_exact (R4): the empty notes in a row that the next
# request's note counts are its row when it is an empty note, else 0
# (decide.rs `NoteCause::row`): the count the cap of empty notes reads
# EXCLUDES: a count of empty notes that stays 0 or resets, so the cap is
#   never reached (the caps laws above are stated over this count); a row
#   of another recovery counted as empty notes
law stop_empty_row_exact:
  for +k: RnRecovery.Rk
  for +row: Nat
  {RnRecovery.Rk.empties(k, row) == rust_empty_row(k, row) : Nat}

# LAW stop_empty_recover_is_rust (R4): what `recover` does with an empty
# reply, under any caps, after any note of any row, is the spec's: the
# next empty note while fewer than 3 empty notes are in a row, else the
# run fails
# EXCLUDES: an empty reply nudged forever (another "1 of 3" note at every
#   row), a cap off by one, a row of another recovery counted
law stop_empty_recover_is_rust:
  for +rc: RnRecovery.RCfg
  for +k: RnRecovery.Rk
  for +row: Nat
  {RnDecision.decide.recover(rc, RnDecision.Emptied{}, k, row) == rust_empty(k, row) : RnDecision.Help}

# LAW stop_empty_example (R4): anchor: an empty reply after no note, then
# after 0, 2, 3 and 100 empty notes in a row, and after 3 length notes
# EXCLUDES: a cap that drifts from 3, an empty row that never grows
law stop_empty_example:
  {[RnDecision.decide.recover(RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnDecision.Emptied{}, RnRecovery.Free{}, 0n), RnDecision.decide.recover(RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnDecision.Emptied{}, RnRecovery.Empties{}, 0n), RnDecision.decide.recover(RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnDecision.Emptied{}, RnRecovery.Empties{}, 2n), RnDecision.decide.recover(RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnDecision.Emptied{}, RnRecovery.Empties{}, 3n), RnDecision.decide.recover(RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnDecision.Emptied{}, RnRecovery.Empties{}, 100n), RnDecision.decide.recover(RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnDecision.Emptied{}, RnRecovery.Longs{}, 3n)] == [RnDecision.Redoes{1n}, RnDecision.Redoes{1n}, RnDecision.Redoes{3n}, RnDecision.Quits{}, RnDecision.Quits{}, RnDecision.Redoes{1n}] : List<&2, RnDecision.Help>}

# Laws: the recoveries' helpers (R9)
# ----------------------------------

# LAW stop_act_runs_exact (R9): an act runs tool calls exactly when it is
# Exec
# EXCLUDES: an Act.runs that is never True, so rec_repeat_never_runs holds
#   vacuously; a pass, a retry, a failure or a compaction read as calls
law stop_act_runs_exact:
  for a: RnRecovery.Act
  {RnRecovery.Act.runs(a) == spec_runs(a) : Bool}

# LAW stop_act_helps_exact (R9): an act does something about the reply
# exactly when it is not Pass
# EXCLUDES: an Act.helps that is always True, so rec_stuck_gets_help holds
#   vacuously; a Pass counted as help
law stop_act_helps_exact:
  for a: RnRecovery.Act
  {RnRecovery.Act.helps(a) == spec_helps(a) : Bool}

# LAW stop_act_reply_exact (R9): the reply each act makes, for every reply
# as it was, is the spec's: Pass keeps it, Exec runs the calls
# EXCLUDES: a passed reply turned into an error or an overflow, calls
#   that do not run (only Redo, Quit, Shrink and Lower were pinned)
law stop_act_reply_exact:
  for a: RnRecovery.Act
  for pass: RnState.Reply
  {RnRecovery.Act.reply(a, pass) == spec_act_reply(a, pass) : RnState.Reply}

# LAW stop_rec_init_exact (R9): a run starts with no note, no row and no
# round
# EXCLUDES: a run that starts one note into a row, or with a round counted
law stop_rec_init_exact:
  {RnRecovery.Rec.init() == RnRecovery.Rec{RnRecovery.Free{}, 0n, 0n, 0n} : RnRecovery.Rec}

# LAW stop_capped_exact (R9): the cap test of every row of every recovery,
# under any caps, is the spec's
# EXCLUDES: a cap test (the one rec_notes_capped reads) off by one, read
#   from another cap, or one that bounds the row of no note
law stop_capped_exact:
  for +rc: RnRecovery.RCfg
  for +k: RnRecovery.Rk
  for +row: Nat
  {RnRecovery.Rk.capped(rc, k, row) == spec_capped(rc, k, row) : Bool}

# LAW stop_again_exact (R9): the rounds in a row of calls of hash h after
# any round are the spec's
# EXCLUDES: a row that goes on across calls of another hash, or one that
#   never grows (the count the repeat laws' premises read)
law stop_again_exact:
  for +same: Nat
  for +last: Nat
  for +h: Nat
  {RnRecovery.again(same, last, h) == spec_again(same, last, h) : Nat}

# Laws: the ladder of a length stop (R7)
# --------------------------------------
# A length stop here is one that LengthStop continues: with no text, or
# with text at a full window (R10), which takes the first rung.

# LAW stop_think_compacts (R7): a length stop, when the window ran out
# and a compaction can run, compacts and goes again; the row of length
# notes stays as it was
# EXCLUDES: a retry at the same cap while the window is what ran out
#   (the 3 identical retries of v0.10.59), a compaction that spends or
#   resets the length row
law stop_think_compacts:
  for +rc: RnRecovery.RCfg
  for lower: Bool
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  {RnRecovery.Rec.step(rc, RnRecovery.Think{True{}, lower}, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Shrink{}, RnRecovery.Rec{k, row, same, last}} : RnRecovery.Dec}

# LAW stop_think_notes (R7): with no compaction to make, under the cap a
# length stop is retried with the next length note, at the agent's
# thinking level
# EXCLUDES: a ladder that skips the notes, a level dropped before the
#   notes run out, a row that does not count
law stop_think_notes:
  for +rc: RnRecovery.RCfg
  for lower: Bool
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for under: {RnRecovery.below(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc)) == True{} : Bool}
  {RnRecovery.Rec.step(rc, RnRecovery.Think{False{}, lower}, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Longs{}, 1n+RnRecovery.Rk.longs(k, row), same, last}} : RnRecovery.Dec}

# LAW stop_think_lowers_last (R7): at the cap, when a level below the
# agent's exists, the last rung retries once more with the next length
# note, one thinking level lower
# EXCLUDES: a run failed while the lower level was still untried
law stop_think_lowers_last:
  for +rc: RnRecovery.RCfg
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for +at: {Nat.is_eq(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc)) == True{} : Bool}
  {RnRecovery.Rec.step(rc, RnRecovery.Think{False{}, True{}}, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Lower{}, RnRecovery.Rec{RnRecovery.Longs{}, 1n+RnRecovery.Rk.longs(k, row), same, last}} : RnRecovery.Dec}

# LAW stop_think_never_fails_early (R7): while a rung remains (a
# compaction, a note under the cap, the lower level), a length stop never
# fails the run
# EXCLUDES: "The model gave no answer" while a better path exists
law stop_think_never_fails_early:
  for +rc: RnRecovery.RCfg
  for +shrink: Bool
  for +lower: Bool
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for left: {StSpec.rung_left(shrink, lower, RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc)) == True{} : Bool}
  {quits(RnRecovery.Dec.act(RnRecovery.Rec.step(rc, RnRecovery.Think{shrink, lower}, RnRecovery.Rec{k, row, same, last}))) == False{} : Bool}

# LAW stop_think_gives_up (R7): with every rung tried, a length stop
# fails the run, its row as it was
# EXCLUDES: an endless ladder, a retry past the last rung
law stop_think_gives_up:
  for +rc: RnRecovery.RCfg
  for +shrink: Bool
  for +lower: Bool
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for spent: {StSpec.rung_left(shrink, lower, RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc)) == False{} : Bool}
  {RnRecovery.Rec.step(rc, RnRecovery.Think{shrink, lower}, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Quit{}, RnRecovery.Rec{k, row, same, last}} : RnRecovery.Dec}

# LAW stop_think_lowers_once (R7): after the lower rung, a length stop
# with nothing to compact fails the run: the level drops once
# EXCLUDES: a level lowered again and again, a lowered level kept for
#   later replies
law stop_think_lowers_once:
  for +rc: RnRecovery.RCfg
  for lower: Bool
  for +same: Nat
  for +last: Nat
  {RnRecovery.Dec.act(RnRecovery.Rec.step(rc, RnRecovery.Think{False{}, lower}, RnRecovery.Rec{RnRecovery.Longs{}, 1n+RnRecovery.RCfg.long(rc), same, last})) == RnRecovery.Quit{} : RnRecovery.Act}

# LAW stop_long_row_exact (R7): the length notes in a row that the next
# request's note counts are its row when it is a length note, else 0
# (decide.rs `NoteCause::row`): the count every rung of the ladder reads
# EXCLUDES: a count of length notes that stays 0 or resets (an endless
#   ladder), a row of another recovery counted as length notes
law stop_long_row_exact:
  for +k: RnRecovery.Rk
  for +row: Nat
  {RnRecovery.Rk.longs(k, row) == rust_long_row(k, row) : Nat}

# LAW stop_think_recover_is_rust (R7): what `recover` does with a length
# stop, under any caps, after any note of any row, with any window,
# catalog cap, tokens and levels, is the spec's ladder
# EXCLUDES: a rung picked from a miscounted row, a compaction the spec's
#   window test does not allow, a ladder that never fails the run
law stop_think_recover_is_rust:
  for +long: Nat
  for +leak: Nat
  for +redirect: Nat
  for +repeat: Nat
  for +k: RnRecovery.Rk
  for +row: Nat
  for +window: Nat
  for +catalog: Nat
  for +prompt: Nat
  for +out: Nat
  for +cuttable: Bool
  for +lower: Bool
  {RnDecision.decide.recover(RnRecovery.RCfg{long, leak, redirect, repeat}, RnDecision.Thought{window, catalog, prompt, out, cuttable, lower}, k, row) == rust_think(long, k, row, window, catalog, prompt, out, cuttable, lower) : RnDecision.Help}

# LAW stop_lower_spends_a_note (R7): the lower rung is a noted retry: it
# spends a note (its note carries the lower level, so only that one
# request thinks lower) and every run still ends (run_ends)
# EXCLUDES: a lower rung outside the run's budgets, one that ends the run
law stop_lower_spends_a_note:
  for +cfg: RnState.Cfg
  for -pass: RnState.Reply
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +m: Nat
  for +p: Nat
  {RnStep.call(cfg, RnRecovery.Act.reply(RnRecovery.Lower{}, pass), r, c, a, 1n+m, p) == RnState.St{RnState.Prepare{}, r, c, a, m, RnState.Cfg.polls(cfg)} : RnState.St}

# LAW stop_shrink_compacts_once (R7): the compaction rung is the
# overflow's compaction: it spends the generation's one compaction
# EXCLUDES: a compaction outside the run's budgets, two in a generation
law stop_shrink_compacts_once:
  for +cfg: RnState.Cfg
  for -pass: RnState.Reply
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +n: Nat
  for +p: Nat
  {RnStep.call(cfg, RnRecovery.Act.reply(RnRecovery.Shrink{}, pass), r, 1n+c, a, n, p) == RnState.St{RnState.Compact{True{}}, r, c, a, n, p} : RnState.St}

# LAW stop_bound_exact (R7): the window ran out exactly as the spec says
# (an unknown window counts as run out, as omp counts it)
# EXCLUDES: a compaction when the catalog cap stopped the reply; none
#   when the reply filled the window, or when the window is unknown
law stop_bound_exact:
  for +window: Nat
  for +catalog: Nat
  for +prompt: Nat
  for +out: Nat
  {RnRecovery.bound(window, catalog, prompt, out) == StSpec.ran_out(window, catalog, prompt, out) : Bool}

# LAW stop_think_example (R7): anchor: the user's stop (a 262144 window, a
# 16384 cap reached with a 48106 prompt: no compaction) at rows 0 to 4 of
# 3 with a lower level, at row 3 with none; a stop at the window of a
# 200000 window (compacts); an unknown window with a compaction to make
# (compacts) and with none (a note)
# EXCLUDES: a ladder that drifts from the shipped rungs
law stop_think_example:
  {[RnDecision.decide.recover(RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnDecision.Thought{262144n, 16384n, 48106n, 16384n, True{}, True{}}, RnRecovery.Free{}, 0n), RnDecision.decide.recover(RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnDecision.Thought{262144n, 16384n, 48106n, 16384n, True{}, True{}}, RnRecovery.Longs{}, 2n), RnDecision.decide.recover(RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnDecision.Thought{262144n, 16384n, 48106n, 16384n, True{}, True{}}, RnRecovery.Longs{}, 3n), RnDecision.decide.recover(RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnDecision.Thought{262144n, 16384n, 48106n, 16384n, True{}, True{}}, RnRecovery.Longs{}, 4n), RnDecision.decide.recover(RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnDecision.Thought{262144n, 16384n, 48106n, 16384n, True{}, False{}}, RnRecovery.Longs{}, 3n), RnDecision.decide.recover(RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnDecision.Thought{200000n, 64000n, 180000n, 15000n, True{}, True{}}, RnRecovery.Longs{}, 1n), RnDecision.decide.recover(RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnDecision.Thought{200000n, 64000n, 180000n, 15000n, False{}, True{}}, RnRecovery.Longs{}, 1n), RnDecision.decide.recover(RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnDecision.Thought{0n, 64000n, 180000n, 15000n, True{}, True{}}, RnRecovery.Free{}, 0n), RnDecision.decide.recover(RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnDecision.Thought{0n, 64000n, 180000n, 15000n, False{}, True{}}, RnRecovery.Free{}, 0n)] == [RnDecision.Redoes{1n}, RnDecision.Redoes{3n}, RnDecision.Lowers{4n}, RnDecision.Quits{}, RnDecision.Quits{}, RnDecision.Compacts{}, RnDecision.Redoes{2n}, RnDecision.Compacts{}, RnDecision.Redoes{1n}] : List<&2, RnDecision.Help>}

# Laws: the round note (R5)
# -------------------------

# LAW stop_rounds_exact (R5): the round note after any rounds of any cap
# is the spec's
# EXCLUDES: a note too early or too late, rounds left off by one
law stop_rounds_exact:
  for +m: Nat
  for +d: Nat
  {S.rounds(m, d) == StSpec.rounds(m, d) : Maybe<&2, String>}

# LAW stop_rounds_example (R5): anchor: 11 rounds left (no note), 10, 1,
# none left, a cap of 1
# EXCLUDES: a threshold or a count that drifts from the spec
law stop_rounds_example:
  {[S.rounds(250n, 238n), S.rounds(250n, 239n), S.rounds(250n, 248n), S.rounds(3n, 2n), S.rounds(1n, 0n)] == [None{}, Some{"Harness note: 10 tool rounds remain in this turn (maxToolRounds 250). Use them for the remaining work; if the work cannot finish in them, end with a final answer that states what is done and exactly what remains."}, Some{"Harness note: 1 tool round remains in this turn (maxToolRounds 250). Use it for the remaining work; if the work cannot finish in it, end with a final answer that states what is done and exactly what remains."}, Some{"Harness note: no tool round remains in this turn (maxToolRounds 3): a tool call now ends the turn unfinished at the cap. End with a final answer that states what is done and exactly what remains."}, Some{"Harness note: no tool round remains in this turn (maxToolRounds 1): a tool call now ends the turn unfinished at the cap. End with a final answer that states what is done and exactly what remains."}] : List<&2, Maybe<&2, String>>}

# Laws: the entry (R6)
# --------------------

# LAW stop_entry_decides (R6): a request spelled by the grammar, every
# Nat and length within the wire, is answered with the spelled spec
# answer
# EXCLUDES: a field read into another, a tag read as another, a default,
#   an answer spelled another way
law stop_entry_decides:
  for +a: FS.Ask
  for h: {sp_fit(a) == True{} : Bool}
  {FS.ffi(sp_w_ask(a, "")) == sp_w_reply(a) : String}

# LAW stop_entry_left_over (R6): input left over after a spelled request
# answers the error form
# EXCLUDES: trailing input ignored, or read as part of the request
law stop_entry_left_over:
  for +a: FS.Ask
  for +rest: String
  for h: {sp_fit(a) == True{} : Bool}
  for more: {String.is_empty(rest) == False{} : Bool}
  {FS.ffi(sp_w_ask(a, rest)) == Wr.err("stop: malformed request") : String}

# LAW stop_entry_unknown (R6): a tag past 1 is malformed, whatever follows
# EXCLUDES: an unknown request read as a known one (exact error bytes)
law stop_entry_unknown:
  for +n: Nat
  for +rest: String
  {FS.ffi(Wr.put_nat(2n+n, rest)) == Wr.err("stop: malformed request") : String}

# LAW stop_entry_example (R6, R10): anchor: the wire strings Rust sends
# and the answers it reads: a final answer, a pause, a cut reply with
# text and room in a 262144-token window (kept: it stands), the same
# reply at a window that ran out with a compaction to make (LengthStop),
# the same with no compaction to make (dropped), a cut reply with text in
# an unknown window with a compaction to make (LengthStop) and with none
# (dropped), a cut reply with no text (LengthStop), a round note with
# none, an unknown tag, input left over
# EXCLUDES: a field order other than Rust's, another reply spelling
law stop_entry_example:
  {[FS.ffi("0,FTFF0,0,0,0,F"), FS.ffi("0,FTFT0,0,0,0,F"), FS.ffi("0,TTFF262144,32768,69000,4096,T"), FS.ffi("0,TTFF200000,64000,180000,15000,T"), FS.ffi("0,TTFF200000,64000,180000,15000,F"), FS.ffi("0,TTFF0,32768,69000,4096,T"), FS.ffi("0,TTFF0,32768,69000,4096,F"), FS.ffi("0,TFFF262144,32768,69000,4096,T"), FS.ffi("1,250,1,"), FS.ffi("2,"), FS.ffi("1,250,1,x")] == ["0,", "0,", "0,", "1,", "5,", "1,", "5,", "1,", "0,", Wr.err("stop: malformed request"), Wr.err("stop: malformed request")] : List<&2, String>}

# LAW stop_entry_premises_witness (R6): a request of each kind that fits
# exists, and so does input left over
# EXCLUDES: a vacuous entry law whose premise no request meets
law stop_entry_premises_witness:
  {(sp_fit(FS.AskWalk{True{}, True{}, False{}, False{}, 9n, 8n, 7n, 6n, True{}}), (sp_fit(FS.AskRounds{1n, 0n}), String.is_empty("x"))) == (True{}, (True{}, False{})) : Bool & (Bool & Bool)}

# Laws: the reply at a stop (R8)
# ------------------------------
# The walk (bend/stop.bend) composed with the reply the run reads at the
# stop (stop_reply, generation.rs `after_reply`) and the run's model
# (bend/run/step.bend, bend/run/request.bend): every live run at a reply
# (phase call, any counts left), any recovery state and ladder facts.

# LAW stop_stand_answers_once (R8): at every reply of every live run, a
# stop the walk lets stand, with text (any such facts), answers the run:
# the run is answered with its counts as they were and stays so whatever
# inputs follow, and it counts exactly one answer
# EXCLUDES: a standing answer re-requested with a reminder (duplicate
#   final reports), a second answer
#   after the first, a standing reply read as a retry or a failure
law stop_stand_answers_once:
  for +cfg: RnState.Cfg
  for +f: S.Facts
  for stands: {S.walk(f) == S.Stands{} : S.Pick}
  for said: {S.Facts.text(f) == True{} : Bool}
  for +rc: RnRecovery.RCfg
  for +k: RnRecovery.Rk
  for +row: Nat
  for +w: Nat
  for +ca: Nat
  for +pr: Nat
  for +o: Nat
  for +cu: Bool
  for +lo: Bool
  for +fin: RnState.Fin
  for +got: RnState.Got
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +n: Nat
  for +p: Nat
  for +more: List<&2, RnState.Ev>
  {RnStep.run.go(RnState.Go{stop_reply(S.walk(f), f, rc, k, row, w, ca, pr, o, cu, lo), fin, got} <> more, cfg, RnState.St{RnState.Call{}, r, c, a, n, p}) == RnState.St{RnState.Answered{}, r, c, a, n, p} : RnState.St} &
  {answers.go(RnState.Go{stop_reply(S.walk(f), f, rc, k, row, w, ca, pr, o, cu, lo), fin, got} <> more, cfg, RnState.St{RnState.Call{}, r, c, a, n, p}) == 1n : Nat}

# LAW stop_stand_sends_no_request (R8): at every reply of every live run,
# after a stop the walk lets stand with text the run sends no further
# request: the requests it sent, cut and will note stay exactly as they
# were, whatever inputs follow
# EXCLUDES: a request after the final answer (a reminder, a retry, a
#   noted retry), a standing answer counted as a cut request
law stop_stand_sends_no_request:
  for +cfg: RnState.Cfg
  for +f: S.Facts
  for stands: {S.walk(f) == S.Stands{} : S.Pick}
  for said: {S.Facts.text(f) == True{} : Bool}
  for +rc: RnRecovery.RCfg
  for +k: RnRecovery.Rk
  for +row: Nat
  for +w: Nat
  for +ca: Nat
  for +pr: Nat
  for +o: Nat
  for +cu: Bool
  for +lo: Bool
  for +fin: RnState.Fin
  for +got: RnState.Got
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +n: Nat
  for +p: Nat
  for +more: List<&2, RnState.Ev>
  for +t: RnRequest.Reqs
  {RnRequest.reqs.go(RnState.Go{stop_reply(S.walk(f), f, rc, k, row, w, ca, pr, o, cu, lo), fin, got} <> more, cfg, RnState.St{RnState.Call{}, r, c, a, n, p}, t) == t : RnRequest.Reqs}

# LAW stop_goes_never_answers (R8): at every reply of every live run, a
# stop the walk does not let stand never answers the run, whatever the
# recovery state and the ladder's facts: its reply is a retry (noted or
# not), a failure or the overflow's compaction, and the step is no answer
# EXCLUDES: a cut, empty or markup reply taken as the answer after a
#   Director continued it, a recovery that passes a continued reply on as
#   the answer
law stop_goes_never_answers:
  for +cfg: RnState.Cfg
  for +f: S.Facts
  for +d: S.Dir
  for goes: {S.walk(f) == S.Goes{d} : S.Pick}
  for +rc: RnRecovery.RCfg
  for +k: RnRecovery.Rk
  for +row: Nat
  for +w: Nat
  for +ca: Nat
  for +pr: Nat
  for +o: Nat
  for +cu: Bool
  for +lo: Bool
  for +fin: RnState.Fin
  for +got: RnState.Got
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +n: Nat
  for +p: Nat
  {retried(stop_reply(S.walk(f), f, rc, k, row, w, ca, pr, o, cu, lo)) == True{} : Bool} &
  {answered(RnState.St.ph(RnStep.step(cfg, RnState.St{RnState.Call{}, r, c, a, n, p}, RnState.Go{stop_reply(S.walk(f), f, rc, k, row, w, ca, pr, o, cu, lo), fin, got}))) == False{} : Bool}

# LAW stop_stand_example (R8): anchor: the replies the run reads at a
# hand-off answer, at an answer while work runs (both stand: the answer),
# at an empty reply (a noted retry), at the empty reply that reaches its
# cap (a failure)
# EXCLUDES: vacuous premises (facts that stand with text, facts that go,
#   exist), a stop_reply that drifts from the shipped walk
law stop_stand_example:
  {[stop_reply(S.walk(S.Facts{False{}, True{}, False{}, False{}, False{}, False{}}), S.Facts{False{}, True{}, False{}, False{}, False{}, False{}}, RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnRecovery.Free{}, 0n, 0n, 0n, 0n, 0n, False{}, False{}), stop_reply(S.walk(S.Facts{False{}, True{}, False{}, True{}, False{}, False{}}), S.Facts{False{}, True{}, False{}, True{}, False{}, False{}}, RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnRecovery.Free{}, 0n, 0n, 0n, 0n, 0n, False{}, False{}), stop_reply(S.walk(S.Facts{False{}, False{}, False{}, False{}, False{}, False{}}), S.Facts{False{}, False{}, False{}, False{}, False{}, False{}}, RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnRecovery.Free{}, 0n, 0n, 0n, 0n, 0n, False{}, False{}), stop_reply(S.walk(S.Facts{False{}, False{}, False{}, False{}, False{}, False{}}), S.Facts{False{}, False{}, False{}, False{}, False{}, False{}}, RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnRecovery.Empties{}, 3n, 0n, 0n, 0n, 0n, False{}, False{})] == [RnState.Plain{}, RnState.Plain{}, RnState.Error{False{}, True{}}, RnState.Error{False{}, False{}}] : List<&2, RnState.Reply>}
