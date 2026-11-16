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
# by eukhe-cli after the headless_exit rule, with the cause it gave and
# the run's goal). spec/durable/headless_task.bend states the rule in
# words (T1-T3) and its wire (W6-W8). Every input is free: any cause, any
# goal, any string.
#
# R1: an answered run whose goal is open is incomplete, and exits 1; no
#     other run is.
# R2: every other run's exit stands: the code headless_exit gave its
#     cause, and the task stands.
# R3: the code is 0 exactly when headless_exit gave 0 and the run did not
#     answer with its goal open.
# R4: the entry answers each request Rust writes (W6) with the spelling
#     (W7) of the core's exit for it, and any input that is not exactly
#     one request with exactly `E headless_task: malformed request`.

# Laws: the task (R1-R3)
# ----------------------

# LAW headless_task_incomplete_iff_unfinished (R1): the task is
# incomplete exactly when the run's exit says it answered while its goal
# is open (SpT.unfinished)
# EXCLUDES: an open goal hidden behind an answer (the overclaim: a run
#   that reports items left exits 0), a run without a goal, with its goal
#   complete or with a failure read as incomplete
law headless_task_incomplete_iff_unfinished:
  for +f: Ht.Facts
  {SpT.incomplete(Ht.decide(f)) == SpT.unfinished(f) : Bool}

# LAW headless_task_unfinished_exits_one (R1): an answered run whose goal
# is open exits 1 as incomplete
# EXCLUDES: an unfinished task that exits 0, or exits 1 with its exit
#   read as standing
law headless_task_unfinished_exits_one:
  for +f: Ht.Facts
  for h: {SpT.unfinished(f) == True{} : Bool}
  {Ht.decide(f) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}

# LAW headless_task_exit_stands (R2): every other run exits as
# headless_exit decided: the code of its cause, the task standing
# EXCLUDES: a failure turned into exit 0 by a complete goal, a
#   budget-limited run turned into a failure by its open goal, a
#   question answered without a goal turned into a failure
law headless_task_exit_stands:
  for +f: Ht.Facts
  for h: {SpT.unfinished(f) == False{} : Bool}
  {Ht.decide(f) == Ht.Verdict{Hx.code(SpT.cause_of(f)), Ht.Stands{}} : Ht.Verdict}

# LAW headless_task_zero_only_when_finished (R3): the code is 0 exactly
# when headless_exit's code is 0 and the run did not answer with its goal
# open
# EXCLUDES: exit 0 for an unfinished task or for a failure; exit 1 for a
#   finished task with no failure
law headless_task_zero_only_when_finished:
  for +f: Ht.Facts
  {Nat.is_eq(SpT.code_of(Ht.decide(f)), 0n) == Bool.and(Nat.is_eq(Hx.code(SpT.cause_of(f)), 0n), Bool.not(SpT.unfinished(f))) : Bool}

# LAW headless_task_example (R1-R3): anchor: an answer with its goal open
# exits 1 incomplete; an answer without a goal and one with its goal
# complete exit 0; a budget-limited run with its goal open exits 0; a
# model error and a give-up exit 1 whatever the goal
# EXCLUDES: an exit other than T1-T3 give for these facts
law headless_task_example:
  {[Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}}), Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}}), Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}}), Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}}), Ht.decide(Ht.Facts{Hx.CRunFailed{Hx.ModelError{}}, Ht.Open{}}), Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Complete{}})] == [Ht.Verdict{1n, Ht.Incomplete{}}, Ht.Verdict{0n, Ht.Stands{}}, Ht.Verdict{0n, Ht.Stands{}}, Ht.Verdict{0n, Ht.Stands{}}, Ht.Verdict{1n, Ht.Stands{}}, Ht.Verdict{1n, Ht.Stands{}}] : List<&2, Ht.Verdict>}

# Laws: the entry (R4)
# --------------------

# LAW headless_task_entry_answers (R4): the entry answers every request
# Rust spells (W6) with the spelling (W7) of the core's exit for it
# EXCLUDES: a cause or a goal misread, a reason lost on the way, a task
#   tag of the other task, a default
law headless_task_entry_answers:
  for +f: Ht.Facts
  {FHt.ffi(SpT.w_task_req(f, "")) == SpT.w_verdict(Ht.decide(f), "") : String}

# LAW headless_task_entry_malformed_exact (R4): every input that is not
# exactly one request (an unknown cause or goal tag, a malformed field,
# input left over) gets exactly the error form 'E ', then
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
# the replies it reads: an answer with its goal open, without a goal, a
# model error with its goal open, a budget-limited run with its goal
# open; an unknown goal, an unknown cause, a short request, input left
# over
# EXCLUDES: another spelling of a request or a reply
law headless_task_entry_example:
  {[FHt.ffi("0,2,"), FHt.ffi("0,0,"), FHt.ffi("3,0,2,"), FHt.ffi("10,2,"), FHt.ffi("0,3,"), FHt.ffi("12,0,"), FHt.ffi("0,"), FHt.ffi("0,2,x")] == ["1,1,", "0,0,", "1,0,", "0,0,", Wr.err("headless_task: malformed request"), Wr.err("headless_task: malformed request"), Wr.err("headless_task: malformed request"), Wr.err("headless_task: malformed request")] : List<&2, String>}
