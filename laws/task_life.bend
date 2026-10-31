# eukhe: the laws of area task_life

import Base
import ../bend/task_life.bend as Tl
import ../bend/ffi_task_life.bend as FTl
import ../bend/submission.bend as Sb
import ../bend/wire.bend as Wr
import ../spec/durable/task_life.bend as Sp
import ../spec/durable/task_life_wire.bend as SpW

# (T1) The lifecycle of a durable task
# ------------------------------------
# bend/task_life.bend, run as the compiled core by bend/ffi_task_life.bend
# (eukhe-bend rules/task_life.rs; asked by the eukhe-durable scheduler,
# harness/scheduler/life.rs, for every task transition it writes, the
# resume of a stored state, the failFast check of a wait, and every abort
# mark). spec/durable/task_life.bend restates pi-durable's rules (S1-S8)
# without the code. Every input is free: any state, transition, handle,
# policy, mark and list.
#
# R1: a transition gives the state of S1-S4 or refuses it with the reason
#     (terminal: ended; completing: held; a commit or handover of a task
#     that is not running: not running; a finalize of a task that holds
#     no outcome: not held).
# R2: resume is S5. R3: join is S6. R4: merge is S7, cascade is S8.
# R5: a submission's status only moves forward: queued, placed, then done
#     or unanswered (types/submissions.rs SubmissionStatus).
# R6: the entry answers each request Rust writes (every handle and count
#     within the wire) with the rules' decision spelled as Rust reads it,
#     and any input that is not exactly one request (an unknown tag, a
#     malformed field, input left over) with exactly the error form
#     `E task_life: malformed request`.

# Laws: the transitions (R1)
# --------------------------

# LAW task_life_step_refines_spec (R1): every transition of every state is
# the spec's, by transition first
# EXCLUDES: a held task reserved or re-settled, a pending or waiting task
#   committing or handed back, an outcome made terminal while owned work
#   holds it (or held when none does), a checkpoint or outcome handle
#   swapped for another, a refusal with another reason
law task_life_step_refines_spec:
  for +s: Tl.St
  for +e: Tl.Ev
  {Tl.step(s, e) == Sp.step_spec(s, e) : Result<&2, &2, Tl.Why, Tl.St>}

# LAW task_life_terminal_absorbs (S1): a terminal task refuses every
# transition as ended, and resume keeps it
# EXCLUDES: a terminal task reopened, re-settled with another outcome,
#   reserved again after a restart, or checked as a wait
law task_life_terminal_absorbs:
  for +o: Tl.Outcome
  for e: Tl.Ev
  {Tl.step(Tl.Terminal{o}, e) == Fail{Tl.Ended{}} : Result<&2, &2, Tl.Why, Tl.St>} & {Tl.resume(Tl.Terminal{o}) == (Tl.Terminal{o}, False{}) : Tl.St & Bool}

# LAW task_life_outcome_once (S4): from a task holding outcome o, every
# transition keeps o: refused, still held, or terminal with o itself
# EXCLUDES: a finalization that writes another outcome, a held task sent
#   back to a live state, a second outcome written over a held one
law task_life_outcome_once:
  for +o: Tl.Outcome
  for e: Tl.Ev
  {Sp.outcome_after(Tl.step(Tl.Completing{o}, e), o) == Some{o} : Maybe<&2, Tl.Outcome>}

# LAW task_life_forward_only (S2-S5): no transition and no resume lowers
# the measure (pending, running or waiting, completing, terminal), but a
# running task put back to pending at its own checkpoint
# EXCLUDES: a terminal or held task made live, a running task requeued at
#   another checkpoint, a resume that loses progress
law task_life_forward_only:
  for +s: Tl.St
  for e: Tl.Ev
  {Sp.forward_ok(s, Tl.step(s, e)) == True{} : Bool} & {Sp.forward_ok(s, Done{Sp.resumed(Tl.resume(s))}) == True{} : Bool}

# Laws: resume (R2)
# -----------------

# LAW task_life_resume_keeps_checkpoint (S5): resume keeps every checkpoint
# and outcome, and leaves no task running
# EXCLUDES: a resumed task restarted from scratch or another checkpoint, a
#   running state kept without its invocation, an outcome dropped
law task_life_resume_keeps_checkpoint:
  for +s: Tl.St
  {Sp.st_cp(Sp.resumed(Tl.resume(s))) == Sp.st_cp(s) : Maybe<&2, Nat>} & {Sp.st_out(Sp.resumed(Tl.resume(s))) == Sp.st_out(s) : Maybe<&2, Tl.Outcome>} & {Sp.is_running(Sp.resumed(Tl.resume(s))) == False{} : Bool}

# LAW task_life_resume_exact (S5): the resume of every state is the spec's,
# the failFast check included
# EXCLUDES: an allSettled wait checked as failFast, a failFast wait not
#   checked again after a restart, a policy changed
law task_life_resume_exact:
  for +s: Tl.St
  {Tl.resume(s) == Sp.resume_spec(s) : Tl.St & Bool}

# Laws: join (R3)
# ---------------

# LAW task_life_join_fail_fast (S6): a failFast wait may run once no
# awaited task is live; after a failure it marks each live awaited task
# that did not fail, and nothing before one
# EXCLUDES: a wait resumed while an awaited task is live, the failed task
#   aborted over its own outcome, an ended task marked, marks without a
#   failure, a mark dropped or out of order
law task_life_join_fail_fast:
  for +live: List<&2, Bool>
  for +failed: List<&2, Bool>
  {Tl.join(Tl.FailFast{}, live, failed) == Sp.join_ff_spec(live, failed) : Bool & List<&2, Bool>}

# LAW task_life_join_all_settled (S6): an allSettled wait may run once no
# awaited task is live, and marks nothing
# EXCLUDES: an allSettled wait that aborts its peers after a failure, or
#   resumes before every awaited task ended
law task_life_join_all_settled:
  for +live: List<&2, Bool>
  for +failed: List<&2, Bool>
  {Tl.join(Tl.AllSettled{}, live, failed) == Sp.join_as_spec(live, failed) : Bool & List<&2, Bool>}

# Laws: abort marks (R4)
# ----------------------

# LAW task_life_mark_merge (S7): adding a mark keeps the stronger: a
# request over a restart mark over none
# EXCLUDES: a request downgraded to a restart mark (an abandoned task's
#   cleanup orphaned or kept waiting), a mark cleared
law task_life_mark_merge:
  for +a: Tl.Mark
  for +b: Tl.Mark
  {Tl.merge(a, b) == Sp.merge_spec(a, b) : Tl.Mark}

# LAW task_life_abort_reaches_owned (S8): a cascade marks exactly each live
# foreground task its owner's walk reached, only below a live owner with
# intent, with the owner's reason merged in; every other task keeps its
# mark
# EXCLUDES: a background or ended task marked, a task marked below an owner
#   without intent or a terminal one, a restart reason passed on by a
#   failed or requesting owner, a reached live task missed, rows reordered
law task_life_abort_reaches_owned:
  for +s: Tl.St
  for +m: Tl.Mark
  for +rs: List<&2, Tl.Row>
  {Tl.cascade(s, m, rs) == Sp.cascade_spec(s, m, rs) : List<&2, Tl.Mark>}

# Laws: submissions (R5)
# ----------------------

# LAW task_life_submission_forward (R5): every change of every submission
# (bend/submission.bend, the rule the session commits run) moves its
# status strictly forward or leaves it: queued, placed, then done or
# unanswered, never back
# EXCLUDES: a settled submission reopened or re-settled the other way, a
#   placed input queued again, a move that keeps the status
law task_life_submission_forward:
  for +s: Sb.Sub
  for c: Sb.Change
  {Sp.sub_forward(s, Sb.step(s, c)) == True{} : Bool}

# LAW task_life_example (R1-R4): anchor: the scheduler's sequence: a
# pending task reserved, its outcome held while owned work lives, then
# finalized; a handover; a restart; a failFast wait after a failure; a
# request over a restart mark
# EXCLUDES: a spec that drifts from the Rust it replaced
law task_life_example:
  {Tl.step(Tl.Pending{7n}, Tl.Reserve{}) == Done{Tl.Running{7n}} : Result<&2, &2, Tl.Why, Tl.St>} &
  {Tl.step(Tl.Running{7n}, Tl.Commit{Tl.NEnd{Tl.Outcome{Tl.RCompleted{}, 1n}}, True{}}) == Done{Tl.Completing{Tl.Outcome{Tl.RCompleted{}, 1n}}} : Result<&2, &2, Tl.Why, Tl.St>} &
  {Tl.step(Tl.Completing{Tl.Outcome{Tl.RCompleted{}, 1n}}, Tl.Finalize{False{}}) == Done{Tl.Terminal{Tl.Outcome{Tl.RCompleted{}, 1n}}} : Result<&2, &2, Tl.Why, Tl.St>} &
  {Tl.step(Tl.Running{7n}, Tl.Requeue{}) == Done{Tl.Pending{7n}} : Result<&2, &2, Tl.Why, Tl.St>} &
  {Tl.step(Tl.Waiting{7n, Tl.FailFast{}}, Tl.Commit{Tl.NRun{8n}, False{}}) == Fail{Tl.NotRunning{}} : Result<&2, &2, Tl.Why, Tl.St>} &
  {Tl.resume(Tl.Running{7n}) == (Tl.Pending{7n}, False{}) : Tl.St & Bool} &
  {Tl.join(Tl.FailFast{}, [True{}, False{}, True{}], [False{}, True{}, True{}]) == (False{}, [True{}, False{}, False{}]) : Bool & List<&2, Bool>} &
  {Tl.merge(Tl.Restart{}, Tl.Request{}) == Tl.Request{} : Tl.Mark}

# Laws: the entry (R6)
# --------------------

# LAW task_life_entry_answers (R6): the entry answers every request Rust
# spells, every handle and count within the wire, with the rules'
# decision spelled as Rust reads it
# EXCLUDES: a field misread or swapped (a checkpoint and an outcome
#   handle, live and failed flags, the owner's mark and a row's), a tag of
#   another state, transition or mark, a reply spelled otherwise, a default
law task_life_entry_answers:
  for +q: FTl.Req
  for fit: {SpW.fit_req(q) == True{} : Bool}
  {FTl.ffi(SpW.w_req(q, "")) == SpW.w_reply(q) : String}

# LAW task_life_entry_reads (R6): the laws' reader reads every spelled
# request that fits the wire back whole, so task_life_entry_malformed_exact
# refuses only what Rust never writes
# EXCLUDES: a reader (and so an entry) that refuses a request Rust writes
law task_life_entry_reads:
  for +q: FTl.Req
  for fit: {SpW.fit_req(q) == True{} : Bool}
  {SpW.read(SpW.w_req(q, "")) == Some{q} : Maybe<&2, FTl.Req>}

# LAW task_life_entry_malformed_exact (R6): every input that is not exactly
# one request (an unknown tag, a malformed field, input left over) gets
# exactly the error form 'E ', then "task_life: malformed request"
# EXCLUDES: a decision made on input that is no request, another error
#   text, a default
law task_life_entry_malformed_exact:
  for +s: String
  for no: {SpW.read(s) == None{} : Maybe<&2, FTl.Req>}
  {FTl.ffi(s) == Wr.err("task_life: malformed request") : String}

# LAW task_life_entry_example (R6): anchor: the strings Rust sends and the
# replies it reads: a reservation, a commit held then not, a terminal
# task's refusal, resumes, a failFast join, a merge, a cascade; input left
# over and an unknown tag
# EXCLUDES: another spelling of a request or a reply
law task_life_entry_example:
  {[FTl.ffi("0,0,7,0,"), FTl.ffi("0,1,7,1,2,0,9,T"), FTl.ffi("0,1,7,1,2,0,9,F"), FTl.ffi("0,4,0,0,0,"), FTl.ffi("1,1,5,"), FTl.ffi("1,2,5,0,"), FTl.ffi("2,0,3,TFF3,FTF"), FTl.ffi("3,1,2,"), FTl.ffi("4,3,1,0,0,3,TF0,FF1,TT0,"), FTl.ffi("0,0,7,0,x"), FTl.ffi("9,")] == ["1,1,7,", "1,3,0,9,", "1,4,0,9,", "0,0,", "0,5,F", "2,5,0,T", "F3,TFF", "2,", "3,2,1,0,", Wr.err("task_life: malformed request"), Wr.err("task_life: malformed request")] : List<&2, String>}
