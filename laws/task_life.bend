# eukhe: the laws of area task_life

import Base
import ../bend/task_life.bend as Tl
import ../bend/ffi_task_life.bend as FTl
import ../bend/submission.bend as Sb
import ../bend/wire.bend as Wr
import ../spec/durable/task_life.bend as Sp
import ../spec/durable/task_life_wire.bend as SpW
import ./base.bend as LawsBase

# (T1) The lifecycle of a durable task
# ------------------------------------
# bend/task_life.bend, run as the compiled core by bend/ffi_task_life.bend
# (eukhe-bend rules/task_life.rs; asked by the eukhe-durable scheduler,
# harness/scheduler/life.rs, for every task transition it writes, the
# resume of a stored state, the failFast check of a wait, and every abort
# mark). spec/durable/task_life.bend restates pi-durable's rules (S1-S8)
# and names the terms the laws use (a state's checkpoint and outcome, the
# i-th flag of a list, a count, a mark's rank); no spec helper decides a
# transition. Every input is free: any state, transition, handle, policy,
# mark and list. (oh-my-pi has no durable task scheduler: the source of
# these rules is pi-durable's spec §5.1-§5.5 and the Rust host.)
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
# A1: a join reads the i-th failed flag as unset when the failed list is
#     shorter than the live list (Rust sends both of one length; the
#     rules stay total on any pair of lists).

# Laws: the transitions (R1)
# --------------------------

# LAW task_life_live_steps (R1, S2, S4): a live task without an outcome
# (pending, running or waiting at checkpoint c) is reserved to run at c;
# an outcome the scheduler writes for it is held (completing) when owned
# work holds it, else terminal, the same outcome either way; a finalize
# of it is refused: not held
# EXCLUDES: a reservation at another checkpoint or into another state, a
#   settle that drops or swaps the outcome or ignores the hold, a live task
#   finalized or refused for another reason
law task_life_live_steps:
  for +s: Tl.St
  for +c: Nat
  for +o: Tl.Outcome
  for h: Bool
  for live: {Sp.st_cp(s) == Some{c} : Maybe<&2, Nat>}
  {Tl.step(s, Tl.Reserve{}) == Done{Tl.Running{c}} : Result<&2, &2, Tl.Why, Tl.St>} & ({Tl.step(s, Tl.Settle{o, True{}}) == Done{Tl.Completing{o}} : Result<&2, &2, Tl.Why, Tl.St>} & ({Tl.step(s, Tl.Settle{o, False{}}) == Done{Tl.Terminal{o}} : Result<&2, &2, Tl.Why, Tl.St>} & {Tl.step(s, Tl.Finalize{h}) == Fail{Tl.NotHeld{}} : Result<&2, &2, Tl.Why, Tl.St>}))

# LAW task_life_only_running_commits (R1, S3): a live task that holds no
# outcome and is not running (pending or waiting) neither commits nor is
# handed back: both are refused as not running
# EXCLUDES: a pending or waiting task committing a checkpoint, a wait or an
#   outcome, a waiting task requeued, another refusal reason
law task_life_only_running_commits:
  for +s: Tl.St
  for n: Tl.Next
  for h: Bool
  for live: {Sp.st_out(s) == None{} : Maybe<&2, Tl.Outcome>}
  for idle: {Sp.is_running(s) == False{} : Bool}
  {Tl.step(s, Tl.Commit{n, h}) == Fail{Tl.NotRunning{}} : Result<&2, &2, Tl.Why, Tl.St>} & {Tl.step(s, Tl.Requeue{}) == Fail{Tl.NotRunning{}} : Result<&2, &2, Tl.Why, Tl.St>}

# LAW task_life_running_commits (R1, S3, S4): a running task at checkpoint
# c commits the state it names: a checkpoint d (running at d), a wait
# (waiting at d with its policy), an outcome (held when owned work holds
# it, else terminal, the same outcome); handed back, it is pending at its
# own checkpoint c
# EXCLUDES: a commit that keeps the old checkpoint, drops or swaps the
#   policy or the outcome, ignores the hold; a handover at another
#   checkpoint or into another state
law task_life_running_commits:
  for +c: Nat
  for +d: Nat
  for p: Tl.Policy
  for +o: Tl.Outcome
  for +h: Bool
  {Tl.step(Tl.Running{c}, Tl.Commit{Tl.NRun{d}, h}) == Done{Tl.Running{d}} : Result<&2, &2, Tl.Why, Tl.St>} & ({Tl.step(Tl.Running{c}, Tl.Commit{Tl.NWait{d, p}, h}) == Done{Tl.Waiting{d, p}} : Result<&2, &2, Tl.Why, Tl.St>} & ({Tl.step(Tl.Running{c}, Tl.Commit{Tl.NEnd{o}, True{}}) == Done{Tl.Completing{o}} : Result<&2, &2, Tl.Why, Tl.St>} & ({Tl.step(Tl.Running{c}, Tl.Commit{Tl.NEnd{o}, False{}}) == Done{Tl.Terminal{o}} : Result<&2, &2, Tl.Why, Tl.St>} & {Tl.step(Tl.Running{c}, Tl.Requeue{}) == Done{Tl.Pending{c}} : Result<&2, &2, Tl.Why, Tl.St>})))

# LAW task_life_held_steps (R1, S2, S4): a task holding outcome o runs no
# code and takes no other outcome: a reservation, a commit, a handover
# and a settle are refused as held; a finalize keeps o held when owned
# work still holds it, else makes o itself terminal
# EXCLUDES: a held task reserved, committed, requeued or re-settled, a
#   finalize that ends a task owned work still holds or writes another
#   outcome, another refusal reason
law task_life_held_steps:
  for +o: Tl.Outcome
  for n: Tl.Next
  for q: Tl.Outcome
  for +h: Bool
  {Tl.step(Tl.Completing{o}, Tl.Reserve{}) == Fail{Tl.Held{}} : Result<&2, &2, Tl.Why, Tl.St>} & ({Tl.step(Tl.Completing{o}, Tl.Commit{n, h}) == Fail{Tl.Held{}} : Result<&2, &2, Tl.Why, Tl.St>} & ({Tl.step(Tl.Completing{o}, Tl.Requeue{}) == Fail{Tl.Held{}} : Result<&2, &2, Tl.Why, Tl.St>} & ({Tl.step(Tl.Completing{o}, Tl.Settle{q, h}) == Fail{Tl.Held{}} : Result<&2, &2, Tl.Why, Tl.St>} & ({Tl.step(Tl.Completing{o}, Tl.Finalize{True{}}) == Done{Tl.Completing{o}} : Result<&2, &2, Tl.Why, Tl.St>} & {Tl.step(Tl.Completing{o}, Tl.Finalize{False{}}) == Done{Tl.Terminal{o}} : Result<&2, &2, Tl.Why, Tl.St>}))))

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

# LAW task_life_resume_moves_only_running (R2, S5): resume leaves every
# state that is not running exactly as it was (a wait keeps its policy),
# and puts a running task at checkpoint c back to pending at c
# EXCLUDES: a wait turned pending or its policy changed, a pending task
#   made a wait, a held outcome finalized by a restart, a running task made
#   a wait or put at another checkpoint
law task_life_resume_moves_only_running:
  for +s: Tl.St
  for +c: Nat
  for idle: {Sp.is_running(s) == False{} : Bool}
  {Sp.resumed(Tl.resume(s)) == s : Tl.St} & {Sp.resumed(Tl.resume(Tl.Running{c})) == Tl.Pending{c} : Tl.St}

# LAW task_life_resume_rechecks_fail_fast (R2, S5): resume asks for the
# failFast check of every waiting task whose policy is failFast
# EXCLUDES: a failFast wait not checked again after a restart (its failed
#   peers never abort the rest)
law task_life_resume_rechecks_fail_fast:
  for +c: Nat
  {Sp.recheck(Tl.resume(Tl.Waiting{c, Tl.FailFast{}})) == True{} : Bool}

# LAW task_life_resume_rechecks_only_fail_fast (R2, S5): resume asks for
# the failFast check only of a waiting task whose policy is failFast
# EXCLUDES: an allSettled wait, a pending, running, held or terminal task
#   checked as failFast
law task_life_resume_rechecks_only_fail_fast:
  for +s: Tl.St
  for yes: {Sp.recheck(Tl.resume(s)) == True{} : Bool}
  exs c: Nat
  {s == Tl.Waiting{c, Tl.FailFast{}} : Tl.St}

# Laws: join (R3)
# ---------------

# LAW task_life_join_may_run (R3, S6): under either policy, a waiting task
# may run exactly when none of its awaited tasks is live (no live flag is
# set), and the join gives one mark per awaited task
# EXCLUDES: a wait resumed while an awaited task is live, a wait kept
#   blocked once none is, a mark dropped or added
law task_life_join_may_run:
  for +p: Tl.Policy
  for +live: List<&2, Bool>
  for +failed: List<&2, Bool>
  {Sp.may_run(Tl.join(p, live, failed)) == Nat.is_eq(Sp.count(live), 0n) : Bool} & {List.length(&2, Bool, Sp.marks(Tl.join(p, live, failed))) == List.length(&2, Bool, live) : Nat}

# LAW task_life_join_marks_live_unfailed (R3, S6, A1): under either
# policy, the join marks awaited task i only when task i is live and did
# not fail
# EXCLUDES: an ended task marked, the failed task aborted over its own
#   outcome, a mark shifted to another task
law task_life_join_marks_live_unfailed:
  for +p: Tl.Policy
  for +live: List<&2, Bool>
  for +failed: List<&2, Bool>
  for +i: Nat
  for hit: {Sp.at(Sp.marks(Tl.join(p, live, failed)), i) == True{} : Bool}
  {Sp.at(live, i) == True{} : Bool} & {Sp.at(failed, i) == False{} : Bool}

# LAW task_life_join_all_settled_quiet (R3, S6): an allSettled wait marks
# no awaited task, whatever failed
# EXCLUDES: an allSettled wait that aborts its peers after a failure
law task_life_join_all_settled_quiet:
  for live: List<&2, Bool>
  for failed: List<&2, Bool>
  {Sp.count(Sp.marks(Tl.join(Tl.AllSettled{}, live, failed))) == 0n : Nat}

# LAW task_life_join_fail_fast_quiet (R3, S6): a failFast wait marks no
# awaited task while none of them failed
# EXCLUDES: marks without a failure (peers aborted for nothing)
law task_life_join_fail_fast_quiet:
  for live: List<&2, Bool>
  for +failed: List<&2, Bool>
  for none: {Sp.count(failed) == 0n : Nat}
  {Sp.count(Sp.marks(Tl.join(Tl.FailFast{}, live, failed))) == 0n : Nat}

# LAW task_life_join_fail_fast_aborts (R3, S6, A1): once some awaited task
# j failed, a failFast wait marks every awaited task i that is live and
# did not fail
# EXCLUDES: a live peer left running after a failure, only the peers after
#   (or before) the failed one marked
law task_life_join_fail_fast_aborts:
  for +live: List<&2, Bool>
  for +failed: List<&2, Bool>
  for +i: Nat
  for j: Nat
  for one: {Sp.at(failed, j) == True{} : Bool}
  for up: {Sp.at(live, i) == True{} : Bool}
  for ok: {Sp.at(failed, i) == False{} : Bool}
  {Sp.at(Sp.marks(Tl.join(Tl.FailFast{}, live, failed)), i) == True{} : Bool}

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

# LAW task_life_cascade_keeps_others (R4, S8): a cascade answers, at every
# position i that holds no live foreground reached task (an ended or
# background task, or past the last reached task), that task's own mark
# (nothing past the last), whatever the owner
# EXCLUDES: a background or ended task marked, a mark added past the
#   reached tasks, rows reordered
law task_life_cascade_keeps_others:
  for +s: Tl.St
  for +m: Tl.Mark
  for +rs: List<&2, Tl.Row>
  for +i: Nat
  for idle: {Sp.hit_at(rs, i) == False{} : Bool}
  {List.get(&2, Tl.Mark, Tl.cascade(s, m, rs), i) == Sp.row_mark(List.get(&2, Tl.Row, rs, i)) : Maybe<&2, Tl.Mark>}

# LAW task_life_cascade_needs_intent (R4, S8): an owner without
# cancellation intent (terminal, or live with no mark and no outcome other
# than completed) leaves every reached task's mark as it was
# EXCLUDES: a task marked below a terminal owner, or below a live owner
#   that neither was marked nor failed
law task_life_cascade_needs_intent:
  for +s: Tl.St
  for +m: Tl.Mark
  for +rs: List<&2, Tl.Row>
  for calm: {Bool.or(Sp.is_terminal(s), Bool.and(Nat.is_eq(Sp.mark_rank(m), 0n), Bool.not(Sp.bad_end(s)))) == True{} : Bool}
  {Tl.cascade(s, m, rs) == Sp.own_marks(rs) : List<&2, Tl.Mark>}

# LAW task_life_cascade_request (R4, S8): below a live owner that holds a
# request mark, or holds an outcome other than completed, every reached
# live foreground task gets a request mark
# EXCLUDES: a requesting or failed owner passing a restart mark (or none),
#   a reached live task missed
law task_life_cascade_request:
  for +s: Tl.St
  for +m: Tl.Mark
  for +rs: List<&2, Tl.Row>
  for +i: Nat
  for k: Tl.Mark
  for row: {List.get(&2, Tl.Row, rs, i) == Some{Tl.Row{True{}, False{}, k}} : Maybe<&2, Tl.Row>}
  for live: {Sp.is_terminal(s) == False{} : Bool}
  for why: {Bool.or(Nat.is_eq(Sp.mark_rank(m), 2n), Sp.bad_end(s)) == True{} : Bool}
  {List.get(&2, Tl.Mark, Tl.cascade(s, m, rs), i) == Some{Tl.Request{}} : Maybe<&2, Tl.Mark>}

# LAW task_life_cascade_restart (R4, S7, S8): below a live owner abandoned
# after a restart (its restart mark) that holds no outcome other than
# completed, every reached live foreground task's mark becomes the
# stronger (merge_spec) of its own and restart
# EXCLUDES: a restart reason upgraded to a request, a reached task's
#   request downgraded to restart, a reached live task missed
law task_life_cascade_restart:
  for +s: Tl.St
  for +rs: List<&2, Tl.Row>
  for +i: Nat
  for +k: Tl.Mark
  for row: {List.get(&2, Tl.Row, rs, i) == Some{Tl.Row{True{}, False{}, k}} : Maybe<&2, Tl.Row>}
  for live: {Sp.is_terminal(s) == False{} : Bool}
  for calm: {Sp.bad_end(s) == False{} : Bool}
  {List.get(&2, Tl.Mark, Tl.cascade(s, Tl.Restart{}, rs), i) == Some{Sp.merge_spec(k, Tl.Restart{})} : Maybe<&2, Tl.Mark>}

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

# LAW task_life_entry_exact (R6): every input the entry does not answer
# with the error form is exactly one request spelled as Rust spells it,
# every handle and count within the wire, with nothing after it
# EXCLUDES: an answer for input that is no request (an unknown tag, a
#   malformed field, a list cut short, input left over), a request read
#   in another field order
law task_life_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FTl.ffi(s)) == False{} : Bool}
  exs q: FTl.Req
  {s == SpW.w_req(q, "") : String} & {SpW.fit_req(q) == True{} : Bool}

# LAW task_life_entry_refuses (R6): every error the entry answers is
# exactly `E task_life: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law task_life_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FTl.ffi(s)) == True{} : Bool}
  {FTl.ffi(s) == Wr.err("task_life: malformed request") : String}

# LAW task_life_entry_example (R6): anchor: the strings Rust sends and the
# replies it reads: a reservation, a commit held then not, a terminal
# task's refusal, resumes, a failFast join, a merge, a cascade; input left
# over and an unknown tag
# EXCLUDES: another spelling of a request or a reply
law task_life_entry_example:
  {[FTl.ffi("0,0,7,0,"), FTl.ffi("0,1,7,1,2,0,9,T"), FTl.ffi("0,1,7,1,2,0,9,F"), FTl.ffi("0,4,0,0,0,"), FTl.ffi("1,1,5,"), FTl.ffi("1,2,5,0,"), FTl.ffi("2,0,3,TFF3,FTF"), FTl.ffi("3,1,2,"), FTl.ffi("4,3,1,0,0,3,TF0,FF1,TT0,"), FTl.ffi("0,0,7,0,x"), FTl.ffi("9,")] == ["1,1,7,", "1,3,0,9,", "1,4,0,9,", "0,0,", "0,5,F", "2,5,0,T", "F3,TFF", "2,", "3,2,1,0,", Wr.err("task_life: malformed request"), Wr.err("task_life: malformed request")] : List<&2, String>}
