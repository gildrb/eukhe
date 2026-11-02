# eukhe: the proof of LAW cron_take_job_exact
# A job that is not active, or has no next run, stays on both sides. An
# active job with a next run n: by cases on whether n is due (cjt.due),
# then on the schedule (the rolled next run) and the claim on record.

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron_job.bend as CronJob

def cjt.due(b: Bool, +p: Nat, +c: Nat, +i: Nat, s: Cr.Sched, +n: Nat, +k: Nat, cl: Maybe<&2, Cr.Claim>, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {Cr.take.due(b, p, c, i, s, n, k, cl, rs, ss, h) == CronJob.take_due_spec(b, p, c, i, s, n, k, cl, rs, ss, h) : Cr.Job}:
  match b:
    case False{}:
      {==}
    case True{}:
      match s:
        case Cr.Once{d}:
          match cl:
            case None{}:
              {==}
            case Some{x}:
              {==}
        case Cr.Every{q}:
          match cl:
            case None{}:
              {==}
            case Some{x}:
              {==}

def CronJob.cron_take_job_exact(p, c, j):
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match st:
        case Cr.Active{}:
          match nx:
            case None{}:
              {==}
            case Some{+n}:
              cjt.due(Nat.is_le(n, c), p, c, i, s, n, k, cl, rs, ss, h)
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}
