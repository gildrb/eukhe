# eukhe: the laws of area headless_task

import Base
import ../bend/headless_exit.bend as Hx
import ../bend/headless_task.bend as Ht
import ../bend/ffi_headless_task.bend as FHt
import ../bend/wire.bend as Wr
import ../spec/durable/headless_task.bend as SpT

# (D5) A headless run exits 0 only for a finished task
# ----------------------------------------------------
# bend/headless_task.bend, run as the compiled core by
# bend/ffi_headless_task.bend (eukhe-bend rules/headless.rs `task`; asked
# by eukhe-cli after the headless_exit rule, with the cause it gave,
# whether the run acted and the judge's reading of the final answer:
# first unread, then again with the reading when the core asks for it).
# spec/durable/headless_task.bend states the rule in words (T1-T3) and
# its wire (W6-W8). Every input is free: any cause, any fact, any
# reading, any string.
#
# R1: an answered run that acted whose final answer the judge reads as
#     stating work left is incomplete, and exits 1; no other run is.
# R5: an answered run whose answer the judge reads and gave no verdict on
#     is unjudged, and exits 3: never 0, never 1; no other run is.
# R6: the core asks for the judge's reading exactly when the run answered
#     after acting and the reading is not given yet; a run that did not
#     act is never judged and its exit stands.
# R2: every other run's exit stands: the code headless_exit gave its
#     cause, and the task stands.
# R3: the code is 0 exactly when headless_exit gave 0 and the run is
#     neither incomplete, nor unjudged, nor waiting for the judge.
# R4: the entry answers each request Rust writes (W6) with the spelling
#     (W7) of the core's exit for it, and any input that is not exactly
#     one request with exactly `E headless_task: malformed request`.

# Laws: the task (R1-R3, R5, R6)
# ------------------------------

# LAW headless_task_incomplete_iff_unfinished (R1): the task is
# incomplete exactly when the run answered after acting and the judge
# read its final answer as stating work left (SpT.unfinished)
# EXCLUDES: an answer that lists items left hidden behind exit 0 (the
#   overclaim), a question answered read as incomplete, a failure read as
#   incomplete
law headless_task_incomplete_iff_unfinished:
  for +f: Ht.Facts
  {SpT.incomplete(Ht.decide(f)) == SpT.unfinished(f) : Bool}

# LAW headless_task_unjudged_iff_unread (R5): the task is unjudged
# exactly when the judge reads the run's final answer and gave no verdict
# on it (SpT.unjudged)
# EXCLUDES: a judge that failed read as a pass or as work left, a judge
#   failure that matters when the run did not act, or the run failed
#   anyway
law headless_task_unjudged_iff_unread:
  for +f: Ht.Facts
  {SpT.unjudged_task(Ht.decide(f)) == SpT.unjudged(f) : Bool}

# LAW headless_task_asks_iff_unread (R6): the core asks for the judge's
# reading exactly when the run answered after acting and no reading is
# given (SpT.asks)
# EXCLUDES: a judge request for a question answered without acting (a
#   tax on plain use), for a run that failed; a run that acted and ends
#   without the judge being asked
law headless_task_asks_iff_unread:
  for +f: Ht.Facts
  {SpT.ask_task(Ht.decide(f)) == SpT.asks(f) : Bool}

# LAW headless_task_unfinished_exits_one (R1): an answered run with work
# left exits 1 as incomplete
# EXCLUDES: an unfinished task that exits 0, or exits 1 read as another
#   task
law headless_task_unfinished_exits_one:
  for +f: Ht.Facts
  for h: {SpT.unfinished(f) == True{} : Bool}
  {Ht.decide(f) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}

# LAW headless_task_unjudged_exits_three (R5): a run whose final answer
# the judge gave no verdict on exits 3 as unjudged, its own code: never 0
# (done), never 1 (a failure or work left)
# EXCLUDES: a judge that could not run (offline, rate-limited, a failed
#   request, an unreadable reply) letting the run exit 0, or read as the
#   run's failure or as work left
law headless_task_unjudged_exits_three:
  for +f: Ht.Facts
  for h: {SpT.unjudged(f) == True{} : Bool}
  {Ht.decide(f) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}

# LAW headless_task_asks_exits_three (R6): a run waiting for the judge's
# reading asks for it, with the unjudged code until the reading comes
# EXCLUDES: a run that needs the judge exiting 0 unread
law headless_task_asks_exits_three:
  for +f: Ht.Facts
  for h: {SpT.asks(f) == True{} : Bool}
  {Ht.decide(f) == Ht.Verdict{3n, Ht.Ask{}} : Ht.Verdict}

# LAW headless_task_unacted_stands (R6): a run that did not act exits as
# headless_exit decided, whatever the reading: a question answered is
# never judged
# EXCLUDES: plain use taxed or broken by the judge (a judge request, a
#   reading that turns a plain answer into exit 1 or 3)
law headless_task_unacted_stands:
  for +f: Ht.Facts
  for u: {SpT.unacted(f) == True{} : Bool}
  {Ht.decide(f) == Ht.Verdict{Hx.code(SpT.cause_of(f)), Ht.Stands{}} : Ht.Verdict}

# LAW headless_task_exit_stands (R2): every other run exits as
# headless_exit decided: the code of its cause, the task standing
# EXCLUDES: a failure turned into exit 0 by a done answer, a done answer
#   read as a failure, a budget-limited run turned into a failure, a
#   question answered turned into a failure
law headless_task_exit_stands:
  for +f: Ht.Facts
  for h: {SpT.unfinished(f) == False{} : Bool}
  for u: {SpT.unjudged(f) == False{} : Bool}
  for k: {SpT.asks(f) == False{} : Bool}
  {Ht.decide(f) == Ht.Verdict{Hx.code(SpT.cause_of(f)), Ht.Stands{}} : Ht.Verdict}

# LAW headless_task_zero_only_when_finished (R3): the code is 0 exactly
# when headless_exit's code is 0 and the run is neither unfinished, nor
# unjudged, nor waiting for the judge
# EXCLUDES: exit 0 for an unfinished, unjudged or unread task or for a
#   failure; exit 1 or 3 for a finished task with no failure
law headless_task_zero_only_when_finished:
  for +f: Ht.Facts
  {Nat.is_eq(SpT.code_of(Ht.decide(f)), 0n) == Bool.and(Nat.is_eq(Hx.code(SpT.cause_of(f)), 0n), Bool.and(Bool.not(SpT.unfinished(f)), Bool.and(Bool.not(SpT.unjudged(f)), Bool.not(SpT.asks(f))))) : Bool}

# LAW headless_task_example (R1-R6): anchor: an acted answer that states
# no work left exits 0; a budget-limited run exits 0 unread and whatever a
# reading says; a model error and a give-up exit 1; an acted answer that
# states work left exits 1 incomplete, one the judge gave no verdict on
# exits 3 unjudged, one not read yet asks (3); a question answered
# without acting exits 0 unread and whatever a reading says; a give-up
# keeps its cause whatever the judge; a failed command that did not act
# exits 1
# EXCLUDES: an exit other than T1-T3 give for these facts
law headless_task_example:
  {[Ht.decide(Ht.Facts{Hx.CAnswered{}, True{}, Ht.RDone{}}), Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, True{}, Ht.RUnasked{}}), Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, True{}, Ht.RLeft{}}), Ht.decide(Ht.Facts{Hx.CRunFailed{Hx.ModelError{}}, True{}, Ht.RUnasked{}}), Ht.decide(Ht.Facts{Hx.CGaveUp{}, True{}, Ht.RUnasked{}}), Ht.decide(Ht.Facts{Hx.CAnswered{}, True{}, Ht.RLeft{}}), Ht.decide(Ht.Facts{Hx.CAnswered{}, True{}, Ht.RUnjudged{}}), Ht.decide(Ht.Facts{Hx.CAnswered{}, True{}, Ht.RUnasked{}}), Ht.decide(Ht.Facts{Hx.CAnswered{}, False{}, Ht.RUnasked{}}), Ht.decide(Ht.Facts{Hx.CAnswered{}, False{}, Ht.RLeft{}}), Ht.decide(Ht.Facts{Hx.CGaveUp{}, True{}, Ht.RUnjudged{}}), Ht.decide(Ht.Facts{Hx.CCommandFailed{}, False{}, Ht.RUnasked{}})] == [Ht.Verdict{0n, Ht.Stands{}}, Ht.Verdict{0n, Ht.Stands{}}, Ht.Verdict{0n, Ht.Stands{}}, Ht.Verdict{1n, Ht.Stands{}}, Ht.Verdict{1n, Ht.Stands{}}, Ht.Verdict{1n, Ht.Incomplete{}}, Ht.Verdict{3n, Ht.Unjudged{}}, Ht.Verdict{3n, Ht.Ask{}}, Ht.Verdict{0n, Ht.Stands{}}, Ht.Verdict{0n, Ht.Stands{}}, Ht.Verdict{1n, Ht.Stands{}}, Ht.Verdict{1n, Ht.Stands{}}] : List<&2, Ht.Verdict>}

# Laws: the entry (R4)
# --------------------

# LAW headless_task_entry_answers (R4): the entry answers every request
# Rust spells (W6) with the spelling (W7) of the core's exit for it
# EXCLUDES: a cause, the acted fact or a reading misread, a reason lost
#   on the way, a task tag of another task, a default
law headless_task_entry_answers:
  for +f: Ht.Facts
  {FHt.ffi(SpT.w_task_req(f, "")) == SpT.w_verdict(Ht.decide(f), "") : String}

# LAW headless_task_entry_malformed_exact (R4): every input that is not
# exactly one request (an unknown cause or reading tag, a malformed
# field, input left over) gets exactly the error form 'E ', then
# "headless_task: malformed request"
# EXCLUDES: an exit answered for input that is no request, another error
#   text, a default
law headless_task_entry_malformed_exact:
  for +s: String
  for no: {SpT.read_task(s) == None{} : Maybe<&2, Ht.Facts>}
  {FHt.ffi(s) == Wr.err("headless_task: malformed request") : String}

# LAW headless_task_entry_left_over (R4): a spelled request (W6) followed
# by any more input answers exactly the error form
# EXCLUDES: the input after the request ignored or read into a field
law headless_task_entry_left_over:
  for +f: Ht.Facts
  for +ch: Char
  for +t: String
  {FHt.ffi(SpT.w_task_req(f, SCon{ch, t})) == Wr.err("headless_task: malformed request") : String}

# LAW headless_task_entry_example (R4): anchor: the strings Rust sends and
# the replies it reads: an acted answer that states no work left, one not
# read yet, a plain answer that did not act, a model error, a
# budget-limited run, an acted answer that states work left, one the
# judge gave no verdict on; a request with a field before the acted fact,
# an unknown cause, an unknown reading, a malformed acted fact, a short
# request, input left over
# EXCLUDES: another spelling of a request or a reply
law headless_task_entry_example:
  {[FHt.ffi("0,T1,"), FHt.ffi("0,T0,"), FHt.ffi("0,F0,"), FHt.ffi("3,0,T0,"), FHt.ffi("9,T0,"), FHt.ffi("0,T2,"), FHt.ffi("0,T3,"), FHt.ffi("0,0,T0,"), FHt.ffi("11,T0,"), FHt.ffi("0,T4,"), FHt.ffi("0,X0,"), FHt.ffi("0,T"), FHt.ffi("0,T0,x")] == ["0,0,", "3,3,", "0,0,", "1,0,", "0,0,", "1,1,", "3,2,", Wr.err("headless_task: malformed request"), Wr.err("headless_task: malformed request"), Wr.err("headless_task: malformed request"), Wr.err("headless_task: malformed request"), Wr.err("headless_task: malformed request"), Wr.err("headless_task: malformed request")] : List<&2, String>}
