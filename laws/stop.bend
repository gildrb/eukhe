# eukhe: the laws of area stop

import Base
import ../bend/stop.bend as S
import ../bend/ffi_stop.bend as FS
import ../bend/run/state.bend as RnState
import ../bend/run/step.bend as RnStep
import ../bend/run/recovery.bend as RnRecovery
import ../bend/run/decision.bend as RnDecision
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ../spec/harness/stop.bend as StSpec

# (ST) The Directors at a candidate stop
# --------------------------------------
# bend/stop.bend, run as the compiled core by bend/ffi_stop.bend (asked by
# eukhe-durable harness/generation/stop.rs at every reply that ends the
# model's turn with no tool call), and the caps of its Directors in
# bend/run/recovery.bend (asked through decide.rs `recover`). Every input
# is free: any facts, any text, any note, any round count.
#
# R1: the walk is the spec's (spec/harness/stop.bend S1-S4): LengthStop,
#     EmptyStop, MarkupStop, PendingWork, UnexpectedStop, inside to
#     outside; the first that does not pass decides.
# R2: each Director's verdict is the spec's (S3): Continue, Pass or Yield
#     exactly.
# R3: a stop never continues while the reply asks the user something, nor
#     while the session owns running work: both stand (PendingWork never
#     continues).
# R4: the caps (S5): an empty reply is retried with a note at most 3
#     times in a row, then the run fails; an announced step not taken is
#     reminded at most 3 times in a row (the reply stays), then the reply
#     stands; a reminder is a noted retry of the run (H4.7), so it spends
#     a note and every run still ends (run_ends: notes are bounded).
# R5: the notes and the round note are the spec's texts (S6, S7).
# R6: the entry answers each request Rust writes (0 the walk: cut, text,
#     broken, pending, said; 1 a note: the attempt, then 0 a cut reply's
#     tokens, row, cap or 1 an announced step's row; 2 the round note: max,
#     done; every Nat and length within the wire) with the spelled spec
#     answer: the pick (0 stands, 1-5 the Director, inside to outside), the
#     note's text, or the round note (0, none | 1, then the text); reads
#     exactly the request; answers a tag past 2 and input left over with
#     `E stop: malformed request`.

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
        case S.UnexpectedStop{}:
          False{}

# the empty notes and the stop notes in a row that a note of recovery k
# with row `row` makes (decide.rs `recover` over `NoteCause::row`)
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
    case RnRecovery.Promises{}:
      0n

def rust_promise_row(k: RnRecovery.Rk, row: Nat) -> Nat:
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
      0n
    case RnRecovery.Promises{}:
      row

def rust_empty.at(under: Bool, row: Nat) -> RnDecision.Help:
  match under:
    case True{}:
      RnDecision.Redoes{1n+row}
    case False{}:
      RnDecision.Quits{}

def rust_promise.at(under: Bool, row: Nat) -> RnDecision.Help:
  match under:
    case True{}:
      RnDecision.Reminds{1n+row}
    case False{}:
      RnDecision.Stands{}

# R4: what `recover` does with an empty reply and with an announced step,
# after the request whose note counts row notes of the recovery k
def rust_empty(+k: RnRecovery.Rk, +row: Nat) -> RnDecision.Help:
  rust_empty.at(Nat.is_lt(rust_empty_row(k, row), StSpec.empty_cap()), rust_empty_row(k, row))

def rust_promise(+k: RnRecovery.Rk, +row: Nat) -> RnDecision.Help:
  rust_promise.at(Nat.is_lt(rust_promise_row(k, row), StSpec.promise_cap()), rust_promise_row(k, row))

# R6: the spelling of a request and of its answer
def sp_w_facts(f: S.Facts, rest: String) -> String:
  match f:
    case S.Facts{c, t, b, p, s}:
      Wr.put_bool(c, Wr.put_bool(t, Wr.put_bool(b, Wr.put_bool(p, Wr.put_str(s, rest)))))

def sp_w_note(n: S.Note, rest: String) -> String:
  match n:
    case S.Cut{t, r, k}:
      Wr.put_nat(0n, Wr.put_nat(t, Wr.put_nat(r, Wr.put_nat(k, rest))))
    case S.Promised{r}:
      Wr.put_nat(1n, Wr.put_nat(r, rest))

def sp_w_ask(a: FS.Ask, rest: String) -> String:
  match a:
    case FS.AskWalk{f}:
      Wr.put_nat(0n, sp_w_facts(f, rest))
    case FS.AskNote{at, n}:
      Wr.put_nat(1n, Wr.put_nat(at, sp_w_note(n, rest)))
    case FS.AskRounds{m, d}:
      Wr.put_nat(2n, Wr.put_nat(m, Wr.put_nat(d, rest)))

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
        case S.UnexpectedStop{}:
          Wr.put_nat(5n, "")

def sp_w_round(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{t}:
      Wr.put_nat(1n, Wr.put_str(t, ""))

def sp_w_reply(a: FS.Ask) -> String:
  match a:
    case FS.AskWalk{f}:
      sp_w_pick(StSpec.pick(f))
    case FS.AskNote{at, n}:
      Wr.put_str(StSpec.note(at, n), "")
    case FS.AskRounds{m, d}:
      sp_w_round(StSpec.rounds(m, d))

# every Nat and length of the request fits the wire
def sp_fit_note(n: S.Note) -> Bool:
  match n:
    case S.Cut{t, r, k}:
      Bool.and(LawsBase.wire_fits(t), Bool.and(LawsBase.wire_fits(r), LawsBase.wire_fits(k)))
    case S.Promised{r}:
      LawsBase.wire_fits(r)

def sp_fit(a: FS.Ask) -> Bool:
  match a:
    case FS.AskWalk{f}:
      match f:
        case S.Facts{c, t, b, p, s}:
          LawsBase.wire_fits(String.length(s))
    case FS.AskNote{at, n}:
      Bool.and(LawsBase.wire_fits(at), sp_fit_note(n))
    case FS.AskRounds{m, d}:
      Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(d))

# Laws: the walk (R1-R3)
# ----------------------

# LAW stop_walk_refines (R1): the walk at every stop is the spec's
# EXCLUDES: a Director dropped, added or moved in the stack, a verdict
#   read as another, a phrase dropped from or added to a table, the end
#   of the reply read from its start or not folded
law stop_walk_refines:
  for +f: S.Facts
  {S.walk(f) == StSpec.pick(f) : S.Pick}

# LAW stop_verdict_exact (R2): every Director's verdict at every stop is
# the spec's: Continue, Pass or Yield exactly
# EXCLUDES: a Director that yields where it should continue (or the
#   reverse), one that reads another fact
law stop_verdict_exact:
  for +d: S.Dir
  for +f: S.Facts
  {S.verdict(d, f) == StSpec.verdict(d, f) : S.Verdict}

# LAW stop_cut_continues (R1): a reply that hit the output limit never
# stands, whatever else it holds: LengthStop continues it
# EXCLUDES: a cut reply taken as the final answer (generation.rs took
#   one with text as the answer)
law stop_cut_continues:
  for t: Bool
  for b: Bool
  for p: Bool
  for s: String
  {S.walk(S.Facts{True{}, t, b, p, s}) == S.Goes{S.LengthStop{}} : S.Pick}

# LAW stop_empty_continues (R1): a whole reply with no text (a
# thinking-only one) never stands: EmptyStop continues it, work pending
# or not
# EXCLUDES: an empty reply read as an answer, or as a pause
law stop_empty_continues:
  for b: Bool
  for p: Bool
  for s: String
  {S.walk(S.Facts{False{}, False{}, b, p, s}) == S.Goes{S.EmptyStop{}} : S.Pick}

# LAW stop_markup_continues (R1): a whole reply with markup the harness
# could not read never stands: MarkupStop continues it
# EXCLUDES: tool-call markup taken as the final answer
law stop_markup_continues:
  for p: Bool
  for s: String
  {S.walk(S.Facts{False{}, True{}, True{}, p, s}) == S.Goes{S.MarkupStop{}} : S.Pick}

# LAW stop_pending_pauses (R3): a whole, readable reply while the session
# owns running work stands: the stop is a pause, whatever it says
# EXCLUDES: a reminder while a job or a child will wake the session
law stop_pending_pauses:
  for s: String
  {S.walk(S.Facts{False{}, True{}, False{}, True{}, s}) == S.Stands{} : S.Pick}

# LAW stop_asked_stands (R3): a whole, readable reply that asks the user
# something stands, whatever else it says
# EXCLUDES: a reminder that talks over a question to the user
law stop_asked_stands:
  for p: Bool
  for +s: String
  for asked: {StSpec.asks(s) == True{} : Bool}
  {S.walk(S.Facts{False{}, True{}, False{}, p, s}) == S.Stands{} : S.Pick}

# LAW stop_promise_continues (R1): a whole, readable reply that announces
# a next step, asks nothing, with no work running, never stands:
# UnexpectedStop continues it
# EXCLUDES: "I'll commit once it passes." taken as the final answer
law stop_promise_continues:
  for +s: String
  for said: {StSpec.promises(s) == True{} : Bool}
  for asked: {StSpec.asks(s) == False{} : Bool}
  {S.walk(S.Facts{False{}, True{}, False{}, False{}, s}) == S.Goes{S.UnexpectedStop{}} : S.Pick}

# LAW stop_plain_stands (R1): a whole, readable reply that announces no
# next step stands
# EXCLUDES: a reminder after a plain final answer
law stop_plain_stands:
  for p: Bool
  for +s: String
  for plain: {StSpec.promises(s) == False{} : Bool}
  {S.walk(S.Facts{False{}, True{}, False{}, p, s}) == S.Stands{} : S.Pick}

# LAW stop_pending_never_continues (R3): PendingWork never continues a run
# EXCLUDES: a pause turned into a reminder
law stop_pending_never_continues:
  for +f: S.Facts
  {pends(S.walk(f)) == False{} : Bool}

# LAW stop_text_example (R1): anchor: the drill's stop, a plan, a plain
# answer, a word inside a word, the right single quote, a question, an
# offer, a statement
# EXCLUDES: a table that drifts from the phrases the spec lists
law stop_text_example:
  {[S.promises("The suite is running now. I'll commit once it passes."), S.promises("Let me run the tests next."), S.promises("All tests pass and the work is committed."), S.promises("it will run"), S.promises("Now I’ll fix it"), S.asks("Should I commit?"), S.asks("Let me know if you need more."), S.asks("Done.")] == [True{}, True{}, False{}, False{}, True{}, True{}, True{}, False{}] : List<&2, Bool>}

# LAW stop_walk_example (R1, R3): anchor: the drill's stop alone and with
# a job running, an offer, an empty reply, a cut reply
# EXCLUDES: a walk that drifts from the Directors' order
law stop_walk_example:
  {[S.walk(S.Facts{False{}, True{}, False{}, False{}, "The suite is running now. I'll commit once it passes."}), S.walk(S.Facts{False{}, True{}, False{}, True{}, "The suite is running now. I'll commit once it passes."}), S.walk(S.Facts{False{}, True{}, False{}, False{}, "I'll commit it. Let me know."}), S.walk(S.Facts{False{}, False{}, False{}, True{}, ""}), S.walk(S.Facts{True{}, True{}, False{}, False{}, "Done."})] == [S.Goes{S.UnexpectedStop{}}, S.Stands{}, S.Stands{}, S.Goes{S.EmptyStop{}}, S.Goes{S.LengthStop{}}] : List<&2, S.Pick>}

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

# LAW stop_promise_reminds (R4): an announced step not taken, under the
# cap, keeps the reply and asks again with the next stop note
# EXCLUDES: a reply dropped, an answer that ends the run before its cap
law stop_promise_reminds:
  for +rc: RnRecovery.RCfg
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for under: {RnRecovery.below(RnRecovery.Rk.promises(k, row), StSpec.promise_cap()) == True{} : Bool}
  {RnRecovery.Rec.step(rc, RnRecovery.Promise{}, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Remind{}, RnRecovery.Rec{RnRecovery.Promises{}, 1n+RnRecovery.Rk.promises(k, row), same, last}} : RnRecovery.Dec}

# LAW stop_promise_stands (R4): after 3 stop notes in a row, the reply
# stands as the answer
# EXCLUDES: an endless row of reminders, a run failed for an answer
law stop_promise_stands:
  for +rc: RnRecovery.RCfg
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for over: {RnRecovery.below(RnRecovery.Rk.promises(k, row), StSpec.promise_cap()) == False{} : Bool}
  {RnRecovery.Dec.act(RnRecovery.Rec.step(rc, RnRecovery.Promise{}, RnRecovery.Rec{k, row, same, last})) == RnRecovery.Stand{} : RnRecovery.Act}

# LAW stop_remind_spends_a_note (R4): a reminder is a noted retry: it
# spends a note, never a retry, so every run still ends (run_ends counts
# the notes)
# EXCLUDES: a reminder outside the run's budgets, a reminder that ends
#   the run
law stop_remind_spends_a_note:
  for +cfg: RnState.Cfg
  for -pass: RnState.Reply
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +m: Nat
  for +p: Nat
  {RnStep.call(cfg, RnRecovery.Act.reply(RnRecovery.Remind{}, pass), r, c, a, 1n+m, p) == RnState.St{RnState.Prepare{}, r, c, a, m, RnState.Cfg.polls(cfg)} : RnState.St}

# Laws: the texts (R5)
# --------------------

# LAW stop_note_exact (R5): every note is the spec's text
# EXCLUDES: a changed word, a row or cap left out, the limit misnamed
law stop_note_exact:
  for +a: Nat
  for +n: S.Note
  {S.note(a, n) == StSpec.note(a, n) : String}

# LAW stop_note_example (R5): anchor: a stop note, a cut reply's note
# with and without its limit
# EXCLUDES: a spec that drifts from the shipped texts
law stop_note_example:
  {[S.note(2n, S.Promised{1n}), S.note(3n, S.Cut{0n, 1n, 3n}), S.note(4n, S.Cut{8192n, 2n, 3n})] == ["Harness note, attempt 2: you announced more work but ended the turn. The task is incomplete: call the next concrete tool now. If the task is done, give the final answer without announcing more work. Stop note 1 of 3.", "Harness note, attempt 3: your previous reply hit the output limit before it finished, so the harness did not take its cut text as your answer. Reason only about the next step, then call its tool. For a large answer (a file, a document, a long text), write a minimal working version first, then extend it with further edits in this turn. Length note 1 of 3.", "Harness note, attempt 4: your previous reply hit the 8192-token output limit before it finished, so the harness did not take its cut text as your answer. Reason only about the next step, then call its tool. For a large answer (a file, a document, a long text), write a minimal working version first, then extend it with further edits in this turn. Length note 2 of 3."] : List<&2, String>}

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

# LAW stop_entry_unknown (R6): a tag past 2 is malformed, whatever follows
# EXCLUDES: an unknown request read as a known one (exact error bytes)
law stop_entry_unknown:
  for +n: Nat
  for +rest: String
  {FS.ffi(Wr.put_nat(3n+n, rest)) == Wr.err("stop: malformed request") : String}

# LAW stop_entry_example (R6): anchor: the wire strings Rust sends and the
# answers it reads: a walk, a note, a round note with none, an unknown
# tag, input left over
# EXCLUDES: a field order other than Rust's, another reply spelling
law stop_entry_example:
  {[FS.ffi("0,FTFF21,Let me run the tests."), FS.ffi("0,FTFT21,Let me run the tests."), FS.ffi("2,250,1,"), FS.ffi("3,"), FS.ffi("2,250,1,x")] == ["5,", "0,", "0,", Wr.err("stop: malformed request"), Wr.err("stop: malformed request")] : List<&2, String>}

# LAW stop_entry_premises_witness (R6): a request that fits exists, and so
# does input left over
# EXCLUDES: a vacuous entry law whose premise no request meets
law stop_entry_premises_witness:
  {(sp_fit(FS.AskRounds{1n, 0n}), String.is_empty("x")) == (True{}, False{}) : Bool & Bool}
