# eukhe: the laws of area cron (the model's per-job steps, pinned)
#
# The refines laws of laws/cron.bend and laws/cron_user.bend tie the
# model's per-job steps (Cr.take, Cr.recover, Cr.finish, Cr.cancel,
# Cr.resume, Cr.pause, Cr.stop, Cr.delete, Cr.edit) to the store's
# decisions only through `view`: the status, the next run, the failures in
# a row and the claim on record. The view drops the ghost state the D2
# laws read (cron_fires_once, cron_once_finished_after_end,
# cron_backoff_bounded): the runs, the occurrences started and the results
# counted. An audit (after adversary 6) made Cr.take claim a due one-shot
# without adding its occurrence to the occurrences started: a one-shot
# with no start started at most once, so cron_fires_once held, and every
# law still checked. Here each per-job step is pinned, for every job and
# every input, to a spec of the whole job it yields; cron_step_exact
# (laws/cron_step.bend) pins Cr.step to these steps, so the D2 laws speak
# of the specs.
#
# The specs read the terms of laws/cron_terms.bend (has_spec, delay_spec,
# later_spec) and drop_spec of laws/cron_step.bend.

import Base
import ../bend/cron.bend as Cr
import ./cron_terms.bend as CronTerms
import ./cron_step.bend as CronStep

# Terms
# -----

# failed runs in a row after which a repeating job stops
def cap_spec() -> Nat:
  8n

# the next run of a schedule after a run at clock c: none for a one-shot
# Once{d}, 1+k minutes later for an interval Every{k}
def rolled_spec(s: Cr.Sched, +c: Nat) -> Maybe<&2, Nat>:
  match s:
    case Cr.Once{d}:
      None{}
    case Cr.Every{k}:
      Some{Nat.add(c, 1n+k)}

# A claim pass
# ------------

# an active job of next run n, due (n at or before the clock c) or not: a
# job not due stays; a due job with no claim on record is claimed by p at
# n (p runs it, n is the newest occurrence started), its next run rolled;
# a due job with a claim on record only rolls its next run
def take_due_spec(due: Bool, +p: Nat, +c: Nat, i: Nat, +s: Cr.Sched, +n: Nat, k: Nat, cl: Maybe<&2, Cr.Claim>, rs: List<&2, Nat>, ss: List<&2, Nat>, h: List<&2, Cr.Mark>) -> Cr.Job:
  match due:
    case False{}:
      Cr.Job{i, s, Cr.Active{}, Some{n}, k, cl, rs, ss, h}
    case True{}:
      match cl:
        case None{}:
          Cr.Job{i, s, Cr.Active{}, rolled_spec(s, c), k, Some{Cr.Claim{n, p}}, p <> rs, n <> ss, h}
        case Some{x}:
          Cr.Job{i, s, Cr.Active{}, rolled_spec(s, c), k, Some{x}, rs, ss, h}

# a claim pass of p at clock c on job j: only an active job with a next run
# changes (take_due_spec); every other job stays whole
def take_job_spec(+p: Nat, +c: Nat, j: Cr.Job) -> Cr.Job:
  match j:
    case Cr.Job{i, +s, st, nx, k, cl, rs, ss, h}:
      match st:
        case Cr.Active{}:
          match nx:
            case None{}:
              Cr.Job{i, s, Cr.Active{}, None{}, k, cl, rs, ss, h}
            case Some{+n}:
              take_due_spec(Nat.is_le(n, c), p, c, i, s, n, k, cl, rs, ss, h)
        case Cr.Paused{}:
          Cr.Job{i, s, Cr.Paused{}, nx, k, cl, rs, ss, h}
        case Cr.Finished{}:
          Cr.Job{i, s, Cr.Finished{}, nx, k, cl, rs, ss, h}
        case Cr.Cancelled{}:
          Cr.Job{i, s, Cr.Cancelled{}, nx, k, cl, rs, ss, h}

# A recovery
# ----------

# p may clear the claim of o: its own claim it no longer runs (p is not in
# the runs rs), or the claim of a dead process
def clears_spec(+p: Nat, +o: Nat, rs: List<&2, Nat>, dead: List<&2, Nat>) -> Bool:
  Bool.or(Bool.and(Nat.is_eq(o, p), Bool.not(CronTerms.has_spec(p, rs))), CronTerms.has_spec(o, dead))

# a cleared claim x's run ends: an active one-shot is fired again under its
# original request id: it stays active, due at the occurrence x started,
# its start withdrawn (its next fire is the same fire), its failures in a
# row and results counted kept; an active interval stays active with its
# next run
def ended_spec(s: Cr.Sched, i: Nat, nx: Maybe<&2, Nat>, k: Nat, x: Cr.Claim, rs: List<&2, Nat>, ss: List<&2, Nat>, h: List<&2, Cr.Mark>) -> Cr.Job:
  match s:
    case Cr.Once{d}:
      match x:
        case Cr.Claim{oc, o}:
          Cr.Job{i, Cr.Once{d}, Cr.Active{}, Some{oc}, k, None{}, rs, Nil{}, h}
    case Cr.Every{n}:
      Cr.Job{i, Cr.Every{n}, Cr.Active{}, nx, k, None{}, rs, ss, h}

# the claim x on record, cleared (b) or not: a claim not cleared stays; a
# cleared claim goes, and its run ends (ended_spec for an active job, any
# other keeps its status and next run); the runs, the failures in a row
# and the results counted stay, and the occurrences started of every job
# but a one-shot fired again
def recover_go_spec(b: Bool, i: Nat, s: Cr.Sched, st: Cr.Status, nx: Maybe<&2, Nat>, k: Nat, x: Cr.Claim, rs: List<&2, Nat>, ss: List<&2, Nat>, h: List<&2, Cr.Mark>) -> Cr.Job:
  match b:
    case False{}:
      Cr.Job{i, s, st, nx, k, Some{x}, rs, ss, h}
    case True{}:
      match st:
        case Cr.Active{}:
          ended_spec(s, i, nx, k, x, rs, ss, h)
        case Cr.Paused{}:
          Cr.Job{i, s, Cr.Paused{}, nx, k, None{}, rs, ss, h}
        case Cr.Finished{}:
          Cr.Job{i, s, Cr.Finished{}, nx, k, None{}, rs, ss, h}
        case Cr.Cancelled{}:
          Cr.Job{i, s, Cr.Cancelled{}, nx, k, None{}, rs, ss, h}

# a recovery of p, with the dead processes dead, on job j: a job with no
# claim stays; the claim of o goes when p may clear it (recover_go_spec)
def recover_job_spec(+p: Nat, +dead: List<&2, Nat>, j: Cr.Job) -> Cr.Job:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, +rs, ss, h}:
      match cl:
        case None{}:
          Cr.Job{i, s, st, nx, k, None{}, rs, ss, h}
        case Some{x}:
          match x:
            case Cr.Claim{+occ, +o}:
              recover_go_spec(clears_spec(p, o, rs, dead), i, s, st, nx, k, Cr.Claim{occ, o}, rs, ss, h)

# The finish step
# ---------------

# the k-th failed run in a row of an active repeating job, at clock c,
# under the cap or not: under it, the job stays active and runs next at
# the end of the k-th pause or at its next run if later; at the cap, the
# job is paused with no next run; no claim either way
def fail_spec(under: Bool, +c: Nat, i: Nat, s: Cr.Sched, nx: Maybe<&2, Nat>, +k: Nat, rs: List<&2, Nat>, ss: List<&2, Nat>, h: List<&2, Cr.Mark>) -> Cr.Job:
  match under:
    case True{}:
      Cr.Job{i, s, Cr.Active{}, Some{CronTerms.later_spec(nx, Nat.add(c, CronTerms.delay_spec(k)))}, k, None{}, rs, ss, h}
    case False{}:
      Cr.Job{i, s, Cr.Paused{}, None{}, k, None{}, rs, ss, h}

# an active job counts the result o of its run, at clock c, its claim
# released: a one-shot is finished with no next run (a good run zeroes the
# failures in a row and is counted, a failure adds one and is counted, a
# skip neither); an interval Every{n}: a good run zeroes the failures in a
# row, keeps the next run and is counted; a skip runs next 1+n minutes
# after c; a failure adds one, is counted, and backs off (fail_spec)
def counted_spec(s: Cr.Sched, +c: Nat, o: Cr.Out, i: Nat, nx: Maybe<&2, Nat>, +k: Nat, rs: List<&2, Nat>, ss: List<&2, Nat>, h: List<&2, Cr.Mark>) -> Cr.Job:
  match s:
    case Cr.Once{d}:
      match o:
        case Cr.Win{}:
          Cr.Job{i, Cr.Once{d}, Cr.Finished{}, None{}, 0n, None{}, rs, ss, Cr.MWin{} <> h}
        case Cr.Loss{}:
          Cr.Job{i, Cr.Once{d}, Cr.Finished{}, None{}, 1n+k, None{}, rs, ss, Cr.MLoss{} <> h}
        case Cr.Skip{}:
          Cr.Job{i, Cr.Once{d}, Cr.Finished{}, None{}, k, None{}, rs, ss, h}
    case Cr.Every{+n}:
      match o:
        case Cr.Win{}:
          Cr.Job{i, Cr.Every{n}, Cr.Active{}, nx, 0n, None{}, rs, ss, Cr.MWin{} <> h}
        case Cr.Skip{}:
          Cr.Job{i, Cr.Every{n}, Cr.Active{}, Some{Nat.add(c, 1n+n)}, k, None{}, rs, ss, h}
        case Cr.Loss{}:
          fail_spec(Nat.is_lt(1n+k, cap_spec()), c, i, Cr.Every{n}, nx, 1n+k, rs, ss, Cr.MLoss{} <> h)

# the claim x on record is p's (own) or not: another's claim stays; p's
# claim is released: an active job counts the result (counted_spec), any
# other keeps its status, next run, failures in a row and results counted
def finish_own_spec(own: Bool, x: Cr.Claim, +c: Nat, o: Cr.Out, i: Nat, s: Cr.Sched, st: Cr.Status, nx: Maybe<&2, Nat>, k: Nat, rs: List<&2, Nat>, ss: List<&2, Nat>, h: List<&2, Cr.Mark>) -> Cr.Job:
  match own:
    case False{}:
      Cr.Job{i, s, st, nx, k, Some{x}, rs, ss, h}
    case True{}:
      match st:
        case Cr.Active{}:
          counted_spec(s, c, o, i, nx, k, rs, ss, h)
        case Cr.Paused{}:
          Cr.Job{i, s, Cr.Paused{}, nx, k, None{}, rs, ss, h}
        case Cr.Finished{}:
          Cr.Job{i, s, Cr.Finished{}, nx, k, None{}, rs, ss, h}
        case Cr.Cancelled{}:
          Cr.Job{i, s, Cr.Cancelled{}, nx, k, None{}, rs, ss, h}

# the claim on record of a job p ran: none, the job stays (p's run already
# ended); else finish_own_spec on whether it is p's
def finish_claim_spec(cl: Maybe<&2, Cr.Claim>, +p: Nat, +c: Nat, o: Cr.Out, i: Nat, s: Cr.Sched, st: Cr.Status, nx: Maybe<&2, Nat>, k: Nat, rs: List<&2, Nat>, ss: List<&2, Nat>, h: List<&2, Cr.Mark>) -> Cr.Job:
  match cl:
    case None{}:
      Cr.Job{i, s, st, nx, k, None{}, rs, ss, h}
    case Some{x}:
      match x:
        case Cr.Claim{+occ, +w}:
          finish_own_spec(Nat.is_eq(w, p), Cr.Claim{occ, w}, c, o, i, s, st, nx, k, rs, ss, h)

# p runs the job (run) or not: a job p does not run stays whole; else p's
# run ends (p leaves the runs) and its claim is settled (finish_claim_spec)
def finish_run_spec(run: Bool, +p: Nat, +c: Nat, o: Cr.Out, i: Nat, s: Cr.Sched, st: Cr.Status, nx: Maybe<&2, Nat>, k: Nat, cl: Maybe<&2, Cr.Claim>, rs: List<&2, Nat>, ss: List<&2, Nat>, h: List<&2, Cr.Mark>) -> Cr.Job:
  match run:
    case False{}:
      Cr.Job{i, s, st, nx, k, cl, rs, ss, h}
    case True{}:
      finish_claim_spec(cl, p, c, o, i, s, st, nx, k, CronStep.drop_spec(p, rs), ss, h)

# p records the result o of its run of job j at clock c
def finish_job_spec(+p: Nat, +c: Nat, +o: Cr.Out, j: Cr.Job) -> Cr.Job:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, +rs, ss, h}:
      finish_run_spec(CronTerms.has_spec(p, rs), p, c, o, i, s, st, nx, k, cl, rs, ss, h)

# User actions
# ------------

# a cancel: every job not cancelled is cancelled with no next run; a
# cancelled job stays; nothing else changes
def cancel_job_spec(j: Cr.Job) -> Cr.Job:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match st:
        case Cr.Active{}:
          Cr.Job{i, s, Cr.Cancelled{}, None{}, k, cl, rs, ss, h}
        case Cr.Paused{}:
          Cr.Job{i, s, Cr.Cancelled{}, None{}, k, cl, rs, ss, h}
        case Cr.Finished{}:
          Cr.Job{i, s, Cr.Cancelled{}, None{}, k, cl, rs, ss, h}
        case Cr.Cancelled{}:
          Cr.Job{i, s, Cr.Cancelled{}, nx, k, cl, rs, ss, h}

# a resume at clock c: an active or paused interval Every{n} is active,
# runs next 1+n minutes after c, its failures in a row forgotten (zero,
# and a reset counted); a one-shot, a finished or a cancelled job stays
def resume_job_spec(+c: Nat, j: Cr.Job) -> Cr.Job:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match s:
        case Cr.Once{d}:
          Cr.Job{i, Cr.Once{d}, st, nx, k, cl, rs, ss, h}
        case Cr.Every{+n}:
          match st:
            case Cr.Active{}:
              Cr.Job{i, Cr.Every{n}, Cr.Active{}, Some{Nat.add(c, 1n+n)}, 0n, cl, rs, ss, Cr.MReset{} <> h}
            case Cr.Paused{}:
              Cr.Job{i, Cr.Every{n}, Cr.Active{}, Some{Nat.add(c, 1n+n)}, 0n, cl, rs, ss, Cr.MReset{} <> h}
            case Cr.Finished{}:
              Cr.Job{i, Cr.Every{n}, Cr.Finished{}, nx, k, cl, rs, ss, h}
            case Cr.Cancelled{}:
              Cr.Job{i, Cr.Every{n}, Cr.Cancelled{}, nx, k, cl, rs, ss, h}

# a pause: an active or paused job is paused with no next run; a finished
# or cancelled job stays; nothing else changes
def pause_job_spec(j: Cr.Job) -> Cr.Job:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match st:
        case Cr.Active{}:
          Cr.Job{i, s, Cr.Paused{}, None{}, k, cl, rs, ss, h}
        case Cr.Paused{}:
          Cr.Job{i, s, Cr.Paused{}, None{}, k, cl, rs, ss, h}
        case Cr.Finished{}:
          Cr.Job{i, s, Cr.Finished{}, nx, k, cl, rs, ss, h}
        case Cr.Cancelled{}:
          Cr.Job{i, s, Cr.Cancelled{}, nx, k, cl, rs, ss, h}

# a stop: an active or paused job is cancelled with no next run; a
# finished or cancelled job stays; nothing else changes
def stop_job_spec(j: Cr.Job) -> Cr.Job:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match st:
        case Cr.Active{}:
          Cr.Job{i, s, Cr.Cancelled{}, None{}, k, cl, rs, ss, h}
        case Cr.Paused{}:
          Cr.Job{i, s, Cr.Cancelled{}, None{}, k, cl, rs, ss, h}
        case Cr.Finished{}:
          Cr.Job{i, s, Cr.Finished{}, nx, k, cl, rs, ss, h}
        case Cr.Cancelled{}:
          Cr.Job{i, s, Cr.Cancelled{}, nx, k, cl, rs, ss, h}

# a delete: whatever its status, the job is cancelled with no next run;
# nothing else changes
def delete_job_spec(j: Cr.Job) -> Cr.Job:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      Cr.Job{i, s, Cr.Cancelled{}, None{}, k, cl, rs, ss, h}

# an edit to the schedule Every{n} at clock c: an active job takes it and
# runs next 1+n minutes after c; a paused job takes it and stays paused
# with no next run; a finished or cancelled job stays; nothing else changes
def edit_job_spec(+c: Nat, +n: Nat, j: Cr.Job) -> Cr.Job:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match st:
        case Cr.Active{}:
          Cr.Job{i, Cr.Every{n}, Cr.Active{}, Some{Nat.add(c, 1n+n)}, k, cl, rs, ss, h}
        case Cr.Paused{}:
          Cr.Job{i, Cr.Every{n}, Cr.Paused{}, None{}, k, cl, rs, ss, h}
        case Cr.Finished{}:
          Cr.Job{i, s, Cr.Finished{}, nx, k, cl, rs, ss, h}
        case Cr.Cancelled{}:
          Cr.Job{i, s, Cr.Cancelled{}, nx, k, cl, rs, ss, h}

# The fires
# ---------

# the occurrences a job started, the newest first
def starts_spec(j: Cr.Job) -> List<&2, Nat>:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      ss

# a claim pass
def take_spec(e: Cr.Ev) -> Bool:
  match e:
    case Cr.Take{p}:
      True{}
    case _:
      False{}

# the claim of occurrence x a claim pass of p puts on record: p's; no
# other event puts one
def fired_by_spec(e: Cr.Ev, +x: Nat) -> Maybe<&2, Cr.Claim>:
  match e:
    case Cr.Take{p}:
      Some{Cr.Claim{x, p}}
    case _:
      None{}

# Laws
# ----

# LAW cron_take_job_exact (D2.2): for every process, clock and job, the model's claim step (Cr.take) yields exactly the spec's whole job: a due active job with no claim is claimed by p at its next run n, p added to the runs and n to the occurrences started, its next run rolled; a due job with a claim only rolls; every other job stays whole
# EXCLUDES: a claim of a due one-shot that leaves its occurrence out of the occurrences started (the audit's: cron_fires_once held, a one-shot with no start), a claim that leaves p out of the runs, a roll that adds a run or a start, a claim pass that changes the results counted
law cron_take_job_exact:
  for +p: Nat
  for +c: Nat
  for +j: Cr.Job
  {Cr.take(p, c, j) == take_job_spec(p, c, j) : Cr.Job}

# LAW cron_recover_job_exact (D2.2): for every process, dead processes and job, the model's recovery step (Cr.recover) yields exactly the spec's whole job: the claim goes when it is p's own and p no longer runs it, or its owner is dead; then an active one-shot is fired again (active, due at the occurrence its claim started, its start withdrawn); the runs and the results counted stay, and the occurrences started of every job but a one-shot fired again
# EXCLUDES: a recovery that drops or adds a run or a result counted, a start of any job but a one-shot fired again, finishes a repeating job or a one-shot, or clears a live process's claim it still runs
law cron_recover_job_exact:
  for +p: Nat
  for +dead: List<&2, Nat>
  for +j: Cr.Job
  {Cr.recover(p, dead, j) == recover_job_spec(p, dead, j) : Cr.Job}

# LAW cron_finish_job_exact (D2.2): for every process, clock, result and job, the model's finish step (Cr.finish) yields exactly the spec's whole job: a job p does not run stays; else p leaves the runs and its own claim is released, an active job counting the result (a good run and a failure counted in the results, a skip not; a one-shot finished; a failure backs off or stops at the cap)
# EXCLUDES: a finish that keeps p in the runs, forgets or adds a result counted (cron_backoff_bounded reads them), counts a skip, drops a start, or releases another process's claim
law cron_finish_job_exact:
  for +p: Nat
  for +c: Nat
  for +o: Cr.Out
  for +j: Cr.Job
  {Cr.finish(p, c, o, j) == finish_job_spec(p, c, o, j) : Cr.Job}

# LAW cron_cancel_job_exact (D2.2): for every job, the model's cancel (Cr.cancel) yields exactly the spec's whole job: cancelled with no next run unless already cancelled; the claim, the runs, the starts and the results counted stay
# EXCLUDES: a cancel that drops a run, a start or a result counted, or the claim
law cron_cancel_job_exact:
  for +j: Cr.Job
  {Cr.cancel(j) == cancel_job_spec(j) : Cr.Job}

# LAW cron_resume_job_exact (D2.2): for every clock and job, the model's resume (Cr.resume) yields exactly the spec's whole job: an active or paused interval is active, runs next one interval after the clock, its failures in a row zeroed and a reset counted; any other job stays whole
# EXCLUDES: a resume that zeroes the failures in a row without counting a reset (cron_backoff_bounded reads the results), drops a run, a start or a claim
law cron_resume_job_exact:
  for +c: Nat
  for +j: Cr.Job
  {Cr.resume(c, j) == resume_job_spec(c, j) : Cr.Job}

# LAW cron_pause_job_exact (D2.2): for every job, the model's pause (Cr.pause) yields exactly the spec's whole job: an active or paused job is paused with no next run; any other stays; the claim, the runs, the starts and the results counted stay
# EXCLUDES: a pause that drops a run, a start or a result counted
law cron_pause_job_exact:
  for +j: Cr.Job
  {Cr.pause(j) == pause_job_spec(j) : Cr.Job}

# LAW cron_stop_job_exact (D2.2): for every job, the model's stop (Cr.stop) yields exactly the spec's whole job: an active or paused job is cancelled with no next run; any other stays; the claim, the runs, the starts and the results counted stay
# EXCLUDES: a stop that drops a run, a start or a result counted
law cron_stop_job_exact:
  for +j: Cr.Job
  {Cr.stop(j) == stop_job_spec(j) : Cr.Job}

# LAW cron_delete_job_exact (D2.2): for every job, the model's delete (Cr.delete) yields exactly the spec's whole job: cancelled with no next run; the claim, the runs, the starts and the results counted stay
# EXCLUDES: a delete that drops a run, a start or a result counted
law cron_delete_job_exact:
  for +j: Cr.Job
  {Cr.delete(j) == delete_job_spec(j) : Cr.Job}

# LAW cron_edit_job_exact (D2.2): for every clock, interval and job, the model's edit (Cr.edit) yields exactly the spec's whole job: an active or paused job takes the schedule Every{n} (an active one runs next 1+n minutes after the clock, a paused one has no next run); any other stays; the claim, the runs, the starts and the results counted stay
# EXCLUDES: an edit that drops a run, a start or a result counted, or zeroes the failures in a row without a reset counted
law cron_edit_job_exact:
  for +c: Nat
  for +n: Nat
  for +j: Cr.Job
  {Cr.edit(c, n, j) == edit_job_spec(c, n, j) : Cr.Job}

# LAW cron_once_refires (exactly-once fires): after a recovery of p clears the claim of an active one-shot (p's own claim it no longer runs, or a dead process's), the job is active, due again at the occurrence its claim started (the next run it was claimed at), with no claim, its failures in a row and its results counted (its run count) as they were: so the next claim pass claims it and its fire carries the original request id `<kind>:<job id>:<run count>` (the session's inbox dedupes it onto the first fire if that one was admitted); its start is withdrawn, the next fire being the same fire
# EXCLUDES: a one-shot finished without its run (the rule this replaced), a fire again under another run count, due at another time, kept claimed (never claimed again) or with its first start kept
law cron_once_refires:
  for +p: Nat
  for +dead: List<&2, Nat>
  for +i: Nat
  for +d: Nat
  for +nx: Maybe<&2, Nat>
  for +k: Nat
  for +oc: Nat
  for +o: Nat
  for +rs: List<&2, Nat>
  for +ss: List<&2, Nat>
  for +h: List<&2, Cr.Mark>
  for cl: {clears_spec(p, o, rs, dead) == True{} : Bool}
  {Cr.recover(p, dead, Cr.Job{i, Cr.Once{d}, Cr.Active{}, nx, k, Some{Cr.Claim{oc, o}}, rs, ss, h}) == Cr.Job{i, Cr.Once{d}, Cr.Active{}, Some{oc}, k, None{}, rs, Nil{}, h} : Cr.Job}

# LAW cron_fire_claims (one fire per claim): for every event, clock, dead processes and job, a step that starts a fire of the job (adds an occurrence x to the occurrences it started) is a claim pass of a process p, on a job with no claim on record, that puts p's claim of x on record: no fire without a claim, so a one-shot a recovery fired again fires at most once more per claim
# EXCLUDES: a start added by a recovery, a finish, an unwind, a death or a user action; a second start while a claim stands; a start whose claim on record is not the claim pass's own of that occurrence
law cron_fire_claims:
  for +e: Cr.Ev
  for +c: Nat
  for +dead: List<&2, Nat>
  for +j: Cr.Job
  for +x: Nat
  for st: {starts_spec(Cr.job(e, c, dead, j)) == x <> starts_spec(j) : List<&2, Nat>}
  ({take_spec(e) == True{} : Bool} & ({Cr.Job.claim(j) == None{} : Maybe<&2, Cr.Claim>} & {Cr.Job.claim(Cr.job(e, c, dead, j)) == fired_by_spec(e, x) : Maybe<&2, Cr.Claim>}))
