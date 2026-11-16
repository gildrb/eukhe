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
# by eukhe-cli after the headless_exit rule, with the cause it gave, the
# run's goal, whether the run acted and the judge's reading of the final
# answer: first unread, then again with the reading when the core asks
# for it). spec/durable/headless_task.bend states the rule in words
# (T1-T5) and its wire (W6-W8). Every input is free: any cause, any goal,
# any fact, any reading, any string.
#
# R1: an answered run with work left (its goal open, or its answer, which
#     the judge reads, stating work left) is incomplete, and exits 1; no
#     other run is.
# R5: an answered run whose answer the judge reads and gave no verdict on
#     is unjudged, and exits 3: never 0, never 1; no other run is.
# R6: the core asks for the judge's reading exactly when the run answered
#     without an open goal after acting and the reading is not given yet;
#     a run that did not act is never judged and its exit stands.
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
# incomplete exactly when the run's exit says it answered with work left:
# its goal open, or its final answer, which the judge reads (the run
# acted and has no open goal), stating work left (SpT.unfinished)
# EXCLUDES: an open goal or an answer that lists items left hidden behind
#   exit 0 (the overclaim), a goal claimed complete that hides the items
#   its own answer lists, a question answered read as incomplete, a
#   failure read as incomplete
law headless_task_incomplete_iff_unfinished:
  for +f: Ht.Facts
  {SpT.incomplete(Ht.decide(f)) == SpT.unfinished(f) : Bool}

# LAW headless_task_unjudged_iff_unread (R5): the task is unjudged
# exactly when the judge reads the run's final answer and gave no verdict
# on it (SpT.unjudged)
# EXCLUDES: a judge that failed read as a pass or as work left, a judge
#   failure that matters when an open goal decides, the run did not act,
#   or the run failed anyway
law headless_task_unjudged_iff_unread:
  for +f: Ht.Facts
  {SpT.unjudged_task(Ht.decide(f)) == SpT.unjudged(f) : Bool}

# LAW headless_task_asks_iff_unread (R6): the core asks for the judge's
# reading exactly when the run answered without an open goal after acting
# and no reading is given (SpT.asks)
# EXCLUDES: a judge request for a question answered without acting (a
#   tax on plain use), for a run that failed or has its goal open; a run
#   that acted and ends without the judge being asked
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

# LAW headless_task_unacted_stands (R6): a run that did not act and has no
# open goal exits as headless_exit decided, whatever the reading: a
# question answered is never judged
# EXCLUDES: plain use taxed or broken by the judge (a judge request, a
#   reading that turns a plain answer into exit 1 or 3)
law headless_task_unacted_stands:
  for +f: Ht.Facts
  for u: {SpT.unacted(f) == True{} : Bool}
  for o: {SpT.goal_open(SpT.goal_of(f)) == False{} : Bool}
  {Ht.decide(f) == Ht.Verdict{Hx.code(SpT.cause_of(f)), Ht.Stands{}} : Ht.Verdict}

# LAW headless_task_exit_stands (R2): every other run exits as
# headless_exit decided: the code of its cause, the task standing
# EXCLUDES: a failure turned into exit 0 by a complete goal or a done
#   answer, a goal claimed complete with a done answer read as a failure,
#   a budget-limited run turned into a failure, a question answered
#   turned into a failure
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

# LAW headless_task_example (R1-R6): anchor: an answer with its goal open
# exits 1 incomplete; an acted answer without a goal that states no work
# left exits 0; one with its goal claimed complete that lists work left
# exits 1 incomplete (the live runs' overclaim); a budget-limited run with
# its goal open exits 0; a model error and a give-up exit 1 whatever the
# goal; an acted answer without a goal that states work left exits 1, one
# the judge gave no verdict on exits 3 unjudged, one not read yet asks
# (3); a question answered without acting exits 0 unread and whatever a
# reading says; a give-up keeps its cause whatever the judge; an acted
# answer with its goal complete that states no work left exits 0
# EXCLUDES: an exit other than T1-T5 give for these facts
law headless_task_example:
  {[Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, True{}, Ht.RUnasked{}}), Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, True{}, Ht.RDone{}}), Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, True{}, Ht.RLeft{}}), Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, True{}, Ht.RUnasked{}}), Ht.decide(Ht.Facts{Hx.CRunFailed{Hx.ModelError{}}, Ht.Open{}, True{}, Ht.RUnasked{}}), Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Complete{}, True{}, Ht.RUnasked{}}), Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, True{}, Ht.RLeft{}}), Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}), Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}), Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, False{}, Ht.RUnasked{}}), Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, False{}, Ht.RLeft{}}), Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}), Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, True{}, Ht.RDone{}})] == [Ht.Verdict{1n, Ht.Incomplete{}}, Ht.Verdict{0n, Ht.Stands{}}, Ht.Verdict{1n, Ht.Incomplete{}}, Ht.Verdict{0n, Ht.Stands{}}, Ht.Verdict{1n, Ht.Stands{}}, Ht.Verdict{1n, Ht.Stands{}}, Ht.Verdict{1n, Ht.Incomplete{}}, Ht.Verdict{3n, Ht.Unjudged{}}, Ht.Verdict{3n, Ht.Ask{}}, Ht.Verdict{0n, Ht.Stands{}}, Ht.Verdict{0n, Ht.Stands{}}, Ht.Verdict{1n, Ht.Stands{}}, Ht.Verdict{0n, Ht.Stands{}}] : List<&2, Ht.Verdict>}

# Laws: the entry (R4)
# --------------------

# LAW headless_task_entry_answers (R4): the entry answers every request
# Rust spells (W6) with the spelling (W7) of the core's exit for it
# EXCLUDES: a cause, a goal, the acted fact or a reading misread, a
#   reason lost on the way, a task tag of another task, a default
law headless_task_entry_answers:
  for +f: Ht.Facts
  {FHt.ffi(SpT.w_task_req(f, "")) == SpT.w_verdict(Ht.decide(f), "") : String}

# LAW headless_task_entry_malformed_exact (R4): every input that is not
# exactly one request (an unknown cause, goal or reading tag, a malformed
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
# the replies it reads: an answer with its goal open, an acted answer
# that states no work left, one not read yet, a plain answer that did not
# act, a model error with its goal open, a budget-limited run with its
# goal open, an acted answer that states work left, one the judge gave no
# verdict on; an unknown goal, an unknown cause, an unknown reading, a
# malformed acted fact, a short request, input left over
# EXCLUDES: another spelling of a request or a reply
law headless_task_entry_example:
  {[FHt.ffi("0,2,T0,"), FHt.ffi("0,0,T1,"), FHt.ffi("0,0,T0,"), FHt.ffi("0,0,F0,"), FHt.ffi("3,0,2,T0,"), FHt.ffi("10,2,T0,"), FHt.ffi("0,0,T2,"), FHt.ffi("0,0,T3,"), FHt.ffi("0,3,T0,"), FHt.ffi("12,0,T0,"), FHt.ffi("0,0,T4,"), FHt.ffi("0,0,X0,"), FHt.ffi("0,2,T"), FHt.ffi("0,2,T0,x")] == ["1,1,", "0,0,", "3,3,", "0,0,", "1,0,", "0,0,", "1,1,", "3,2,", Wr.err("headless_task: malformed request"), Wr.err("headless_task: malformed request"), Wr.err("headless_task: malformed request"), Wr.err("headless_task: malformed request"), Wr.err("headless_task: malformed request"), Wr.err("headless_task: malformed request")] : List<&2, String>}
