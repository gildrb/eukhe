# eukhe: the proof of LAW cron_finish_job_exact
# The model's membership and its leave of the runs are the spec's
# (LCj.cj.has, LCj.cj.drop); then by cases on whether p runs the job, the
# claim on record, whose it is, the status, the schedule and the result; a
# failure's pause and next run are the spec's (LCj.cj.delay, LCj.cj.later).

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron_job.bend as CronJob
import ../../laws/cron_terms.bend as CronTerms
import ../../laws/cron_step.bend as CronStep
import ./base.bend as LCj

def cjf.fail(b: Bool, +c: Nat, +i: Nat, +s: Cr.Sched, +nx: Maybe<&2, Nat>, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {Cr.finish.fail(b, c, i, s, nx, k, rs, ss, h) == CronJob.fail_spec(b, c, i, s, nx, k, rs, ss, h) : Cr.Job}:
  match b:
    case True{}:
      %LCj.cj.delay(k) : {Cr.Job{i, s, Cr.Active{}, Some{Cr.later(nx, Nat.add(c, Cr.delay(k)))}, k, None{}, rs, ss, h} == Cr.Job{i, s, Cr.Active{}, Some{CronTerms.later_spec(nx, Nat.add(c, _))}, k, None{}, rs, ss, h} : Cr.Job}
      %LCj.cj.later(nx, Nat.add(c, Cr.delay(k))) : {Cr.Job{i, s, Cr.Active{}, Some{Cr.later(nx, Nat.add(c, Cr.delay(k)))}, k, None{}, rs, ss, h} == Cr.Job{i, s, Cr.Active{}, Some{_}, k, None{}, rs, ss, h} : Cr.Job}
      {==}
    case False{}:
      {==}

def cjf.count(s: Cr.Sched, +c: Nat, o: Cr.Out, +i: Nat, +nx: Maybe<&2, Nat>, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {Cr.finish.count(Cr.is_once(s), c, o, i, s, nx, k, rs, ss, h) == CronJob.counted_spec(s, c, o, i, nx, k, rs, ss, h) : Cr.Job}:
  match s:
    case Cr.Once{d}:
      match o:
        case Cr.Win{}:
          {==}
        case Cr.Loss{}:
          {==}
        case Cr.Skip{}:
          {==}
    case Cr.Every{+n}:
      match o:
        case Cr.Win{}:
          {==}
        case Cr.Skip{}:
          {==}
        case Cr.Loss{}:
          cjf.fail(Nat.is_lt(1n+k, Cr.CAP()), c, i, Cr.Every{n}, nx, 1n+k, rs, ss, Cr.MLoss{} <> h)

def cjf.own(b: Bool, +x: Cr.Claim, +c: Nat, +o: Cr.Out, +i: Nat, +s: Cr.Sched, st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {Cr.finish.own(b, x, c, o, i, s, st, nx, k, rs, ss, h) == CronJob.finish_own_spec(b, x, c, o, i, s, st, nx, k, rs, ss, h) : Cr.Job}:
  match b:
    case False{}:
      {==}
    case True{}:
      match st:
        case Cr.Active{}:
          cjf.count(s, c, o, i, nx, k, rs, ss, h)
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

def cjf.claim(cl: Maybe<&2, Cr.Claim>, +p: Nat, +c: Nat, +o: Cr.Out, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {Cr.finish.claim(cl, p, c, o, i, s, st, nx, k, rs, ss, h) == CronJob.finish_claim_spec(cl, p, c, o, i, s, st, nx, k, rs, ss, h) : Cr.Job}:
  match cl:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case Cr.Claim{+occ, +w}:
          cjf.own(Nat.is_eq(w, p), Cr.Claim{occ, w}, c, o, i, s, st, nx, k, rs, ss, h)

def cjf.run(b: Bool, +p: Nat, +c: Nat, +o: Cr.Out, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +cl: Maybe<&2, Cr.Claim>, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {Cr.finish.run(b, p, c, o, i, s, st, nx, k, cl, rs, ss, h) == CronJob.finish_run_spec(b, p, c, o, i, s, st, nx, k, cl, rs, ss, h) : Cr.Job}:
  match b:
    case False{}:
      {==}
    case True{}:
      %LCj.cj.drop(p, rs) : {Cr.finish.claim(cl, p, c, o, i, s, st, nx, k, Cr.drop(p, rs), ss, h) == CronJob.finish_claim_spec(cl, p, c, o, i, s, st, nx, k, _, ss, h) : Cr.Job}
      cjf.claim(cl, p, c, o, i, s, st, nx, k, Cr.drop(p, rs), ss, h)

def CronJob.cron_finish_job_exact(p, c, o, j):
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, +cl, +rs, +ss, +h}:
      %LCj.cj.has(p, rs) : {Cr.finish.run(Cr.has(p, rs), p, c, o, i, s, st, nx, k, cl, rs, ss, h) == CronJob.finish_run_spec(_, p, c, o, i, s, st, nx, k, cl, rs, ss, h) : Cr.Job}
      cjf.run(Cr.has(p, rs), p, c, o, i, s, st, nx, k, cl, rs, ss, h)
