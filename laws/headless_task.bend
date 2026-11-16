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
# run's goal and the judge's reading of the final answer).
# spec/durable/headless_task.bend states the rule in words (T1-T4) and
# its wire (W6-W8). Every input is free: any cause, any goal, any
# reading, any string.
#
# R1: an answered run with work left (its goal open, or without an open
#     goal its answer stating work left) is incomplete, and exits 1; no
#     other run is.
# R5: an answered run without an open goal whose answer the judge gave
#     no verdict on is unjudged, and exits 1; no other run is.
# R2: every other run's exit stands: the code headless_exit gave its
#     cause, and the task stands.
# R3: the code is 0 exactly when headless_exit gave 0 and the run is
#     neither incomplete nor unjudged.
# R4: the entry answers each request Rust writes (W6) with the spelling
#     (W7) of the core's exit for it, and any input that is not exactly
#     one request with exactly `E headless_task: malformed request`.

# Laws: the task (R1-R3, R5)
# --------------------------

# LAW headless_task_incomplete_iff_unfinished (R1): the task is
# incomplete exactly when the run's exit says it answered with work left:
# its goal open, or without an open goal its final answer stating work
# left (SpT.unfinished)
# EXCLUDES: an open goal or an answer that lists items left hidden behind
#   exit 0 (the overclaim), a goal claimed complete that hides the items
#   its own answer lists, a question answered read as incomplete, a
#   failure read as incomplete
law headless_task_incomplete_iff_unfinished:
  for +f: Ht.Facts
  {SpT.incomplete(Ht.decide(f)) == SpT.unfinished(f) : Bool}

# LAW headless_task_unjudged_iff_unread (R5): the task is unjudged
# exactly when the run answered without an open goal and the judge gave
# no verdict on its answer (SpT.unjudged)
# EXCLUDES: a judge that failed read as a pass (exit 0 without a
#   verdict), a judge failure that matters when an open goal decides or
#   the run failed anyway
law headless_task_unjudged_iff_unread:
  for +f: Ht.Facts
  {SpT.unjudged_task(Ht.decide(f)) == SpT.unjudged(f) : Bool}

# LAW headless_task_unfinished_exits_one (R1): an answered run with work
# left exits 1 as incomplete
# EXCLUDES: an unfinished task that exits 0, or exits 1 read as another
#   task
law headless_task_unfinished_exits_one:
  for +f: Ht.Facts
  for h: {SpT.unfinished(f) == True{} : Bool}
  {Ht.decide(f) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}

# LAW headless_task_unjudged_exits_one (R5): an answered run without an
# open goal whose answer the judge gave no verdict on exits 1 as
# unjudged
# EXCLUDES: a broken judge that lets the run exit 0, or reads as
#   incomplete
law headless_task_unjudged_exits_one:
  for +f: Ht.Facts
  for h: {SpT.unjudged(f) == True{} : Bool}
  {Ht.decide(f) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}

# LAW headless_task_exit_stands (R2): every other run exits as
# headless_exit decided: the code of its cause, the task standing
# EXCLUDES: a failure turned into exit 0 by a complete goal or a done
#   answer, a goal claimed complete with a done answer read as a failure, a budget-limited run turned into a failure, a question
#   answered turned into a failure
law headless_task_exit_stands:
  for +f: Ht.Facts
  for h: {SpT.unfinished(f) == False{} : Bool}
  for u: {SpT.unjudged(f) == False{} : Bool}
  {Ht.decide(f) == Ht.Verdict{Hx.code(SpT.cause_of(f)), Ht.Stands{}} : Ht.Verdict}

# LAW headless_task_zero_only_when_finished (R3): the code is 0 exactly
# when headless_exit's code is 0 and the run is neither unfinished nor
# unjudged
# EXCLUDES: exit 0 for an unfinished or unjudged task or for a failure;
#   exit 1 for a finished task with no failure
law headless_task_zero_only_when_finished:
  for +f: Ht.Facts
  {Nat.is_eq(SpT.code_of(Ht.decide(f)), 0n) == Bool.and(Nat.is_eq(Hx.code(SpT.cause_of(f)), 0n), Bool.and(Bool.not(SpT.unfinished(f)), Bool.not(SpT.unjudged(f)))) : Bool}

# LAW headless_task_example (R1-R5): anchor: an answer with its goal open
# exits 1 incomplete; an answer without a goal that states no work left
# exits 0; one with its goal claimed complete that lists work left exits
# 1 incomplete (the live runs' overclaim); a
# budget-limited run with its goal open exits 0; a model error and a
# give-up exit 1 whatever the goal; an answer without a goal that states
# work left exits 1 incomplete, one the judge gave no verdict on exits 1
# unjudged, one the judge was not asked about (no text) exits 0; a
# give-up keeps its cause whatever the judge; an answer with its goal
# complete that states no work left exits 0
# EXCLUDES: an exit other than T1-T4 give for these facts
law headless_task_example:
  {[Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, Ht.RUnasked{}}), Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, Ht.RDone{}}), Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, Ht.RLeft{}}), Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, Ht.RUnasked{}}), Ht.decide(Ht.Facts{Hx.CRunFailed{Hx.ModelError{}}, Ht.Open{}, Ht.RUnasked{}}), Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Complete{}, Ht.RUnasked{}}), Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, Ht.RLeft{}}), Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, Ht.RUnjudged{}}), Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, Ht.RUnasked{}}), Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.NoGoal{}, Ht.RUnjudged{}}), Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, Ht.RDone{}})] == [Ht.Verdict{1n, Ht.Incomplete{}}, Ht.Verdict{0n, Ht.Stands{}}, Ht.Verdict{1n, Ht.Incomplete{}}, Ht.Verdict{0n, Ht.Stands{}}, Ht.Verdict{1n, Ht.Stands{}}, Ht.Verdict{1n, Ht.Stands{}}, Ht.Verdict{1n, Ht.Incomplete{}}, Ht.Verdict{1n, Ht.Unjudged{}}, Ht.Verdict{0n, Ht.Stands{}}, Ht.Verdict{1n, Ht.Stands{}}, Ht.Verdict{0n, Ht.Stands{}}] : List<&2, Ht.Verdict>}

# Laws: the entry (R4)
# --------------------

# LAW headless_task_entry_answers (R4): the entry answers every request
# Rust spells (W6) with the spelling (W7) of the core's exit for it
# EXCLUDES: a cause, a goal or a reading misread, a reason lost on the
#   way, a task tag of another task, a default
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
# the replies it reads: an answer with its goal open, an answer without a
# goal that states no work left, a model error with its goal open, a
# budget-limited run with its goal open, an answer without a goal that
# states work left, one the judge gave no verdict on; an unknown goal, an
# unknown cause, an unknown reading, a short request, input left over
# EXCLUDES: another spelling of a request or a reply
law headless_task_entry_example:
  {[FHt.ffi("0,2,0,"), FHt.ffi("0,0,1,"), FHt.ffi("3,0,2,0,"), FHt.ffi("10,2,0,"), FHt.ffi("0,0,2,"), FHt.ffi("0,0,3,"), FHt.ffi("0,3,0,"), FHt.ffi("12,0,0,"), FHt.ffi("0,0,4,"), FHt.ffi("0,2,"), FHt.ffi("0,2,0,x")] == ["1,1,", "0,0,", "1,0,", "0,0,", "1,1,", "1,2,", Wr.err("headless_task: malformed request"), Wr.err("headless_task: malformed request"), Wr.err("headless_task: malformed request"), Wr.err("headless_task: malformed request"), Wr.err("headless_task: malformed request")] : List<&2, String>}
