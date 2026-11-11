# eukhe: the laws of area cron (the model's per-job steps: the rest of the job)
#
# The refines laws of laws/cron.bend and laws/cron_user.bend tie the
# model's per-job steps (Cr.take, Cr.recover, Cr.finish, Cr.cancel,
# Cr.resume, Cr.pause, Cr.stop, Cr.delete, Cr.edit) to the store's
# decisions only through `view`: the status, the next run, the failures in
# a row and the claim on record. The view drops the job's id, its schedule
# and the ghost state the D2 laws read (cron_fires_once,
# cron_once_finished_after_end, cron_backoff_bounded): the runs, the
# occurrences started and the results counted. An audit (after adversary
# 6) made Cr.take claim a due one-shot without adding its occurrence to
# the occurrences started: a one-shot with no start started at most once,
# so cron_fires_once held, and every law still checked. The laws here
# state, for every job and every input, what each per-job step does to
# that rest of the job: which steps leave it alone, when an occurrence
# starts, when a run ends, when a result or a reset is counted, when the
# schedule changes. With the refines laws they fix the whole job a step
# yields; cron_step_exact (laws/cron_step.bend) pins Cr.step to these
# steps, so the D2 laws speak of them.
#
# The laws read the store's specs (laws/cron_store.bend) on the facts of
# the model job (Cron.fact_of, laws/cron.bend), owns_spec of
# laws/cron_terms.bend and drop_spec of laws/cron_step.bend.

import Base
import ../bend/cron.bend as Cr
import ../bend/cron_store.bend as CS
import ./cron.bend as Cron
import ./cron_store.bend as CronStore
import ./cron_terms.bend as CronTerms
import ./cron_step.bend as CronStep

# Terms
# -----

# the rest of a job, what the view of the refines laws leaves out: its id,
# its schedule, the processes that run it now, the occurrences it started
# (the newest first) and the results it counted (the newest first)
type Rest is Data:
  Rest{id: Nat, sched: Cr.Sched, runs: List<&2, Nat>, starts: List<&2, Nat>, hist: List<&2, Cr.Mark>}

def rest_spec(j: Cr.Job) -> Rest:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      Rest{i, s, rs, ss, h}

# the rest of a job after a claim pass, from the claim on record before
# (was) and after (now): a claim put on a job that had none starts its
# occurrence: its owner joins the runs, its occurrence the occurrences
# started; in every other case the runs and the occurrences started stay;
# the id, the schedule and the results counted stay always
def started_spec(was: Maybe<&2, Cr.Claim>, now: Maybe<&2, Cr.Claim>, r: Rest) -> Rest:
  match was:
    case Some{x}:
      r
    case None{}:
      match now:
        case None{}:
          r
        case Some{x}:
          match x:
            case Cr.Claim{occ, owner}:
              match r:
                case Rest{i, s, rs, ss, h}:
                  Rest{i, s, owner <> rs, occ <> ss, h}

# the results counted after a finish the store answers x: a run it counts
# (Ran) is a failed run when it failed, a good run when not; a skip and an
# untouched job count nothing
def counted_spec(x: CS.Fin, failed: Bool, h: List<&2, Cr.Mark>) -> List<&2, Cr.Mark>:
  match x:
    case CS.Untouched{}:
      h
    case CS.Ran{st, n, k}:
      match failed:
        case True{}:
          Cr.MLoss{} <> h
        case False{}:
          Cr.MWin{} <> h
    case CS.Skipped{st, n, k}:
      h

# the rest of a job after the finish of p's run of it, the store answering
# x: p no longer runs it, the result is counted as the answer says
# (counted_spec); the id, the schedule and the occurrences started stay
def finished_spec(x: CS.Fin, failed: Bool, +p: Nat, r: Rest) -> Rest:
  match r:
    case Rest{i, s, rs, ss, h}:
      Rest{i, s, CronStep.drop_spec(p, rs), ss, counted_spec(x, failed, h)}

# p holds the claim on record of job j
def owned_spec(+p: Nat, j: Cr.Job) -> Bool:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      CronTerms.owns_spec(cl, p)

# the rest of a job after a resume the store answers x: a job that
# resumes (Resumed) counts a reset; an ended or a one-shot job counts
# nothing; the id, the schedule, the runs and the occurrences started stay
def resumed_spec(x: CS.Again, r: Rest) -> Rest:
  match x:
    case CS.Resumed{st, n, k}:
      match r:
        case Rest{i, s, rs, ss, h}:
          Rest{i, s, rs, ss, Cr.MReset{} <> h}
    case CS.Ended{}:
      r
    case CS.NotRecurring{}:
      r

# the rest of a job after an edit to the schedule Every{n} the store
# answers x: a job that takes the edit (Edited) has the schedule Every{n},
# a locked job keeps its own; the id, the runs, the occurrences started
# and the results counted stay
def edited_spec(x: CS.Edit, n: Nat, r: Rest) -> Rest:
  match x:
    case CS.Locked{}:
      r
    case CS.Edited{st, nx}:
      match r:
        case Rest{i, s, rs, ss, h}:
          Rest{i, Cr.Every{n}, rs, ss, h}

# Laws
# ----

# LAW cron_holds_keep_rest (D2.2): for every job, the model's cancel, pause, stop and delete, and its recovery by any process whoever is dead, leave the rest of the job as it was: its id, its schedule, its runs, the occurrences it started and the results it counted
# EXCLUDES: a cancel, pause, stop, delete or recovery that drops or adds a run, a start or a result counted, or changes the job's id or schedule
law cron_holds_keep_rest:
  for +p: Nat
  for +dead: List<&2, Nat>
  for +j: Cr.Job
  {rest_spec(Cr.cancel(j)) == rest_spec(j) : Rest} & {rest_spec(Cr.pause(j)) == rest_spec(j) : Rest} & {rest_spec(Cr.stop(j)) == rest_spec(j) : Rest} & {rest_spec(Cr.delete(j)) == rest_spec(j) : Rest} & {rest_spec(Cr.recover(p, dead, j)) == rest_spec(j) : Rest}

# LAW cron_take_starts_claim (D2.2): for every process, clock and job, the model's claim step (Cr.take) starts an occurrence exactly when it puts a claim on record of a job that had none: then the claim's owner joins the runs and its occurrence the occurrences started (the newest first); in every other case the runs and the occurrences started stay; the id, the schedule and the results counted stay always
# EXCLUDES: a claim of a due job that leaves its occurrence out of the occurrences started (the audit's: cron_fires_once held, a one-shot with no start) or its owner out of the runs, a roll or a job left alone that adds a run or a start, a claim pass that changes the results counted, the id or the schedule
law cron_take_starts_claim:
  for +p: Nat
  for +c: Nat
  for +j: Cr.Job
  {rest_spec(Cr.take(p, c, j)) == started_spec(Cr.Job.claim(j), Cr.Job.claim(Cr.take(p, c, j)), rest_spec(j)) : Rest}

# LAW cron_finish_idle (D2.2): the model's finish step (Cr.finish) of a process that does not run the job changes nothing of it, whatever the clock and the result
# EXCLUDES: a result counted, a claim released or a status changed for a job the finishing process does not run
law cron_finish_idle:
  for +p: Nat
  for +c: Nat
  for +o: Cr.Out
  for +j: Cr.Job
  for idle: {Cr.has(p, Cron.runs_of(j)) == False{} : Bool}
  {Cr.finish(p, c, o, j) == j : Cr.Job}

# LAW cron_finish_unowned (D2.2): the model's finish step of a process p that runs the job while the claim on record is not p's (none, or another process's) only ends p's run, as an unwind does (Cr.unrun): the claim, the status, the next run, the failures in a row, the occurrences started and the results counted stay
# EXCLUDES: a finish that releases another process's claim, or counts a result without the claim
law cron_finish_unowned:
  for +p: Nat
  for +c: Nat
  for +o: Cr.Out
  for +j: Cr.Job
  for run: {Cr.has(p, Cron.runs_of(j)) == True{} : Bool}
  for unowned: {owned_spec(p, j) == False{} : Bool}
  {Cr.finish(p, c, o, j) == Cr.unrun(p, j) : Cr.Job}

# LAW cron_finish_counts_run (D2.2): on a clock of any unit u, the model's finish step of p's run of a job whose claim p holds ends that run (p leaves the runs) and counts the result exactly as the store's finish step answers (a good run: ran, not failed; a failure: ran and failed; a skip: neither): a run the store counts (Ran) is counted, a failed run when it failed and a good run when not; a skip and a job that is not active count nothing; the id, the schedule and the occurrences started stay
# EXCLUDES: a finish that keeps p in the runs, forgets or adds a result counted (cron_backoff_bounded reads them), counts a skip, counts a failure as a good run, or drops a start
law cron_finish_counts_run:
  for +v: Nat
  for +p: Nat
  for +c: Nat
  for +o: Cr.Out
  for +x: Nat
  for +j: Cr.Job
  for run: {Cr.has(p, Cron.runs_of(j)) == True{} : Bool}
  for own: {Cr.Job.claim(j) == Some{Cr.Claim{x, p}} : Maybe<&2, Cr.Claim>}
  {rest_spec(Cr.finish(p, c, o, j)) == finished_spec(CronStore.finish_spec(1n+v, Cron.fact_of(j, 1n+v), Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, 1n+v)), Cron.failed_of(o), p, rest_spec(j)) : Rest}

# LAW cron_resume_counts_reset (D2.2): on a clock of any unit u, the model's resume (Cr.resume) counts a reset exactly when the store's resume resumes the job (Resumed: an active or paused repeating job); an ended or a one-shot job counts nothing; the id, the schedule, the runs and the occurrences started stay
# EXCLUDES: a resume that zeroes the failures in a row without counting a reset (cron_backoff_bounded reads the results), counts a reset for a job it leaves alone, or drops a run or a start
law cron_resume_counts_reset:
  for +v: Nat
  for +c: Nat
  for +j: Cr.Job
  {rest_spec(Cr.resume(c, j)) == resumed_spec(CronStore.resume_spec(Cron.fact_of(j, 1n+v), Nat.mul(c, 1n+v)), rest_spec(j)) : Rest}

# LAW cron_edit_reschedules (D2.2): on a clock of any unit u, the model's edit to the schedule Every{k} at the clock (its first run 1+k minutes later, as Rust computes it) gives the job that schedule exactly when the store's edit takes it (Edited: an active or paused job); a locked job keeps its schedule; the id, the runs, the occurrences started and the results counted stay
# EXCLUDES: an edit that leaves an active or paused job on its old schedule, reschedules a finished or cancelled job, or drops a run, a start or a result counted
law cron_edit_reschedules:
  for +v: Nat
  for +c: Nat
  for +k: Nat
  for +j: Cr.Job
  {rest_spec(Cr.edit(c, k, j)) == edited_spec(CronStore.edit_spec(Cron.fact_of(j, 1n+v), Some{Nat.mul(Nat.add(c, 1n+k), 1n+v)}), k, rest_spec(j)) : Rest}
