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
# bend/run/recovery.bend (asked through bend/ffi_run.bend: decide.rs
# `recover` and `after_reply`; their laws: laws/stop/recover.bend). Every
# input is free: any facts, any window, any round count. Where a rule is
# unclear, the requirement's turn recovery decides.
#
# R1: the walk is the spec's (spec/harness/stop.bend S1-S3): LengthStop,
#     EmptyStop, MarkupStop, PendingWork, inside to outside; the first
#     that does not pass decides. A whole, readable reply stands,
#     whatever it says: its text is no fact of the walk, and a reply that
#     was not cut reads no fact of the window.
# R2: each Director acts on its own facts alone: LengthStop decides a cut
#     reply (R10), EmptyStop continues one with no text, MarkupStop one
#     with markup the harness could not read; PendingWork yields while
#     work is pending. The verdicts are seen only through the walk's pick
#     (the entry answers the pick): the R1 and R10 laws carry R2.
# R3: PendingWork never continues a run: a whole, readable reply with no
#     unread markup stands while the session owns running work (a pause).
#     An empty or markup reply still continues with work pending, and a
#     cut reply is LengthStop's to decide (R10).
# R4: the caps (S4; EMPTY_STOP_MAX_RETRIES = 3): an empty reply is
#     retried with an empty note at most 3 times in a row, the notes
#     counting 1, 2, 3, then the run fails; a note of another recovery
#     between them starts the row again.
# R5: the round note comes once at most 10 tool rounds are left (left =
#     max - 1 - done, at least 0) and names them. The texts are those of
#     the Rust tests (generation/tests/stops.rs `round_note`).
# R6: the entry answers each request Rust writes (0 the walk: cut, text,
#     broken, pending, then the window's facts at a cut reply: window,
#     catalog, prompt, out, cuttable; 1 the round note: max, done; every
#     Nat within the wire) with the spelled spec answer: the pick (0
#     stands, 1-4 the Director, inside to outside, 5 dropped) or the round
#     note (0, none | 1, then the text); reads exactly the request (it
#     accepts only spelled requests); answers a tag past 1 and input left
#     over with `E stop: malformed request`.
# R7: a length stop that LengthStop continues (no text: the model still
#     reasoned; or full, R10) climbs the spec's ladder (S7), never failing
#     the run while a rung remains: compact when the window ran out (the
#     window is unknown, which counts as run out, or the output is below
#     the catalog max output and prompt + output + 8192 reach the window)
#     and a compaction can run, at most once a generation (the row
#     stays); else a length note under the cap; else, once, a length
#     note one thinking level lower; else the run fails. The lower level
#     rides only the noted request (Rust: NoteCause::Length `lowered`; no
#     Bend model, no law). Each rung is a noted retry or the overflow's
#     compaction, spending the run's budgets (bounded: law run_ends of
#     laws/run/model.bend).
# R8: the reply the run reads at a stop (generation.rs `after_reply`,
#     modelled here by stop_reply: the laws' model, tied to Rust by the
#     tests of generation/tests/stops.rs): a stop the walk lets stand
#     with text answers the run once and for good; the run sends no
#     further request and counts one answer, whatever follows. A stop the
#     walk does not let stand never answers the run: its reply is a noted
#     retry, a failure or the overflow's compaction. A dropped stop ends
#     the run as an answer does (R10).
# R9: the recoveries' helpers that the laws of laws/run/recover.bend read
#     are not vacuous: only the act whose reply is the calls runs them
#     (Act.runs); Pass keeps the reply and every other act helps
#     (Act.helps) and is never the answer; a row past its cap is not
#     capped (Rk.capped); the same calls with the same results count one
#     more round in a row each round from a run start, other calls start
#     a row of 1 (again).
# R10: a reply cut at the output limit. With no text it never stands.
#     With text it stands exactly when the window has room (S5: not
#     spent; an unknown window is spent): the truncated reply is kept as
#     the run's answer, whatever else its text holds; it answers the run
#     once and the run sends no further request. With text and a spent
#     window, the run compacts (the overflow's compaction) when a
#     compaction can run, then the request goes again; when none can, the
#     reply is dropped: the run ends with no further request, the reply
#     stays in the transcript but leaves the model's context, and no
#     warning follows it (Rust: generation/round.rs `answer`). Its laws:
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

# the round note comes
def is_some(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{t}:
      True{}

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
# call) of facts f, the walk's pick p: this file's model of generation.rs
# `after_reply` (no shipped Bend code makes it; Rust's side is tied by
# generation/tests/stops.rs): a stop that stands reads the reply as
# Ended.reply made it (no note, no cause), a Director that goes reads its
# recovery's (go_reply, help_reply: the same model); a dropped stop reads
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

# Laws: the caps (R4; the requirement laws: laws/stop/recover.bend)
# -----------------------------------------------------------------

# LAW stop_empty_example (R4): anchor: an empty reply after no note, then
# after 0, 2, 3 and 100 empty notes in a row, and after 3 length notes
# EXCLUDES: a cap that drifts from 3, an empty row that never grows
law stop_empty_example:
  {[RnDecision.decide.recover(RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnDecision.Emptied{}, RnRecovery.Free{}, 0n), RnDecision.decide.recover(RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnDecision.Emptied{}, RnRecovery.Empties{}, 0n), RnDecision.decide.recover(RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnDecision.Emptied{}, RnRecovery.Empties{}, 2n), RnDecision.decide.recover(RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnDecision.Emptied{}, RnRecovery.Empties{}, 3n), RnDecision.decide.recover(RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnDecision.Emptied{}, RnRecovery.Empties{}, 100n), RnDecision.decide.recover(RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnDecision.Emptied{}, RnRecovery.Longs{}, 3n)] == [RnDecision.Redoes{1n}, RnDecision.Redoes{1n}, RnDecision.Redoes{3n}, RnDecision.Quits{}, RnDecision.Quits{}, RnDecision.Redoes{1n}] : List<&2, RnDecision.Help>}

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

# LAW stop_think_lowers_once (R7): after the lower rung (row long + 1), a
# length stop with nothing to compact fails the run: the level drops
# once
# EXCLUDES: a level lowered again and again
law stop_think_lowers_once:
  for +rc: RnRecovery.RCfg
  for lower: Bool
  for +same: Nat
  for +last: Nat
  {RnRecovery.Dec.act(RnRecovery.Rec.step(rc, RnRecovery.Think{False{}, lower}, RnRecovery.Rec{RnRecovery.Longs{}, 1n+RnRecovery.RCfg.long(rc), same, last})) == RnRecovery.Quit{} : RnRecovery.Act}

# LAW stop_lower_spends_a_note (R7): the lower rung's reply is a noted
# retry: with a note left it goes back to prepare a request and spends
# one note of the generation's budget (MAX_NOTES), its counts otherwise
# as they were. Which level the request uses is Rust's (NoteCause::Length
# `lowered`), not stated here
# EXCLUDES: a lower rung outside the run's note budget, one that ends the
#   run while a note is left
law stop_lower_spends_a_note:
  for +cfg: RnState.Cfg
  for -pass: RnState.Reply
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +m: Nat
  for +p: Nat
  {RnStep.call(cfg, RnRecovery.Act.reply(RnRecovery.Lower{}, pass), r, c, a, 1n+m, p) == RnState.St{RnState.Prepare{}, r, c, a, m, RnState.Cfg.polls(cfg)} : RnState.St}

# LAW stop_shrink_compacts_once (R7): the compaction rung's reply is the
# overflow's compaction: with a compaction left it compacts and spends
# it, the other counts as they were (that a generation has one, and none
# after it compacted: stop_shrink_once_a_generation)
# EXCLUDES: a compaction rung that does not compact, or compacts without
#   spending the count
law stop_shrink_compacts_once:
  for +cfg: RnState.Cfg
  for -pass: RnState.Reply
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +n: Nat
  for +p: Nat
  {RnStep.call(cfg, RnRecovery.Act.reply(RnRecovery.Shrink{}, pass), r, 1n+c, a, n, p) == RnState.St{RnState.Compact{True{}}, r, c, a, n, p} : RnState.St}

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

# LAW stop_rounds_example (R5): anchor: 11 rounds left (no note), 10, 1,
# none left, a cap of 1
# EXCLUDES: a threshold or a count that drifts from the spec
law stop_rounds_example:
  {[S.rounds(250n, 238n), S.rounds(250n, 239n), S.rounds(250n, 248n), S.rounds(3n, 2n), S.rounds(1n, 0n)] == [None{}, Some{"Harness note: 10 tool rounds remain in this turn (maxToolRounds 250). Use them for the remaining work; if the work cannot finish in them, end with a final answer that states what is done and exactly what remains."}, Some{"Harness note: 1 tool round remains in this turn (maxToolRounds 250). Use it for the remaining work; if the work cannot finish in it, end with a final answer that states what is done and exactly what remains."}, Some{"Harness note: no tool round remains in this turn (maxToolRounds 3): a tool call now ends the turn unfinished at the cap. End with a final answer that states what is done and exactly what remains."}, Some{"Harness note: no tool round remains in this turn (maxToolRounds 1): a tool call now ends the turn unfinished at the cap. End with a final answer that states what is done and exactly what remains."}] : List<&2, Maybe<&2, String>>}

# LAW stop_rounds_quiet_while_many_left (R5): after any `done` rounds, with
# 11 or more tool rounds left (max = done + 1 + left), no round note
# EXCLUDES: a round note too early (a threshold past 10)
law stop_rounds_quiet_while_many_left:
  for +d: Nat
  for +x: Nat
  {S.rounds(1n+Nat.add(d, 11n+x), d) == None{} : Maybe<&2, String>}

# LAW stop_rounds_note_near_the_cap (R5): after any `done` rounds, with at
# most 10 tool rounds left (max = done + 1 + left), the round note comes
# EXCLUDES: a round note too late (a threshold below 10), rounds left
#   counted off by one
law stop_rounds_note_near_the_cap:
  for +d: Nat
  for +l: Nat
  for near: {Nat.is_le(l, 10n) == True{} : Bool}
  {is_some(S.rounds(1n+Nat.add(d, l), d)) == True{} : Bool}

# LAW stop_rounds_note_once_none_left (R5): once `done` reaches the cap
# (done >= max, any max), the round note still comes
# EXCLUDES: a count of rounds left that wraps or goes silent past the cap
law stop_rounds_note_once_none_left:
  for +m: Nat
  for +x: Nat
  {is_some(S.rounds(m, Nat.add(m, x))) == True{} : Bool}

# LAW stop_texts_rust_example (R5): anchor: the texts the Rust tests pin
# (generation/tests/stops.rs `round_note(2)`, `round_note(1)`,
# `round_note(0)`: maxToolRounds 3 after 0, 1 and 2 rounds)
# EXCLUDES: a text that drifts from what the Rust tests expect
law stop_texts_rust_example:
  {[S.rounds(3n, 0n), S.rounds(3n, 1n), S.rounds(3n, 2n)] == [Some{"Harness note: 2 tool rounds remain in this turn (maxToolRounds 3). Use them for the remaining work; if the work cannot finish in them, end with a final answer that states what is done and exactly what remains."}, Some{"Harness note: 1 tool round remains in this turn (maxToolRounds 3). Use it for the remaining work; if the work cannot finish in it, end with a final answer that states what is done and exactly what remains."}, Some{"Harness note: no tool round remains in this turn (maxToolRounds 3): a tool call now ends the turn unfinished at the cap. End with a final answer that states what is done and exactly what remains."}] : List<&2, Maybe<&2, String>>}

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
# The walk (bend/stop.bend) composed with stop_reply (this file's model of
# generation.rs `after_reply`: the reply Rust makes of the pick and of
# `recover`'s help; trusted, tied to Rust by generation/tests/stops.rs)
# and the run's model (bend/run/step.bend, bend/run/request.bend): every
# live run at a reply (phase call, any counts left), any recovery state
# and ladder facts.

# LAW stop_stand_answers_once (R8): at every reply of every live run, for
# facts the walk lets stand with text, the reply stop_reply models (the
# reply with its text and no call: Plain) answers the run: the run is
# answered with its counts as they were and stays so whatever inputs
# follow, and it counts exactly one answer
# EXCLUDES: a standing answer re-requested with a reminder (duplicate
#   final reports), a second answer after the first, a standing reply
#   read as a retry or a failure (in the run's model; that Rust reads such
#   a stop as Plain is the model's assumption)
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
# after facts the walk lets stand with text (the reply stop_reply models)
# the run sends no further request: the requests it sent, cut and will
# note stay exactly as they were, whatever inputs follow
# EXCLUDES: a request after the final answer (a reminder, a retry, a
#   noted retry), a standing answer counted as a cut request (in the run's
#   model, under stop_reply's assumption)
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

# LAW stop_whole_text_answers (R8): a whole, readable reply with text
# stands with the reply and is read as the run's answer (the reply
# Plain), work pending or not and whatever its window facts (Rust writes
# no window for a reply that was not cut, and the entry reads that window
# of 0 as spent), any recovery state and ladder facts: the facts the walk
# reads, and the text the reply carries, are the reply's own
# EXCLUDES: a whole final answer read as a retry, a failure or a drop
#   because its window facts say spent; a text fact other than the
#   reply's
law stop_whole_text_answers:
  for p: Bool
  for sp: Bool
  for cu: Bool
  for +rc: RnRecovery.RCfg
  for +k: RnRecovery.Rk
  for +row: Nat
  for +w: Nat
  for +ca: Nat
  for +pr: Nat
  for +o: Nat
  for +wc: Bool
  for +lo: Bool
  {S.walk(S.Facts{False{}, True{}, False{}, p, sp, cu}) == S.Stands{} : S.Pick} &
  {stop_reply(S.walk(S.Facts{False{}, True{}, False{}, p, sp, cu}), S.Facts{False{}, True{}, False{}, p, sp, cu}, rc, k, row, w, ca, pr, o, wc, lo) == RnState.Plain{} : RnState.Reply}

# LAW stop_goes_never_answers (R8): at every reply of every live run, for
# facts the walk does not let stand, whatever the recovery state and the
# ladder's facts, the reply stop_reply models (`recover`'s help as
# generation.rs reads it) is a retry (noted or not), a failure or the
# overflow's compaction, and the step after it is no answer
# EXCLUDES: a cut, empty or markup reply taken as the answer after a
#   Director continued it (a Pass from the recoveries reaches Rust as
#   Quits: decision.bend Help.act; that no stuck reply gets Pass is
#   rec_stuck_gets_help's, laws/run/recover.bend)
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

# LAW stop_verdict_exact (R2): every Director's verdict at every stop is
# the spec's: Continue, Pass, Yield or Drop exactly
# EXCLUDES: a Director that yields where it should continue (or the
#   reverse), one that reads another fact
law stop_verdict_exact:
  for +d: S.Dir
  for +f: S.Facts
  {S.verdict(d, f) == StSpec.verdict(d, f) : S.Verdict}

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
