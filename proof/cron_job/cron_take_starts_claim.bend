# eukhe: the proof of LAW cron_take_starts_claim
# A job the claim pass leaves alone, or only rolls, keeps its claim: the
# rest stays (cts.same). A due active job with no claim gets p's claim at
# its next run n: p joins the runs and n the occurrences started.

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron_job.bend as CronJob

# the claim on record did not change: the rest stays
def cts.same(cl: Maybe<&2, Cr.Claim>, +r: CronJob.Rest) -> {r == CronJob.started_spec(cl, cl, r) : CronJob.Rest}:
  match cl:
    case None{}:
      {==}
    case Some{x}:
      {==}

def cts.due(b: Bool, +p: Nat, +c: Nat, +i: Nat, +s: Cr.Sched, +n: Nat, +k: Nat, +cl: Maybe<&2, Cr.Claim>, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {CronJob.rest_spec(Cr.take.due(b, p, c, i, s, n, k, cl, rs, ss, h)) == CronJob.started_spec(cl, Cr.Job.claim(Cr.take.due(b, p, c, i, s, n, k, cl, rs, ss, h)), CronJob.Rest{i, s, rs, ss, h}) : CronJob.Rest}:
  match b:
    case False{}:
      cts.same(cl, CronJob.Rest{i, s, rs, ss, h})
    case True{}:
      match cl:
        case None{}:
          {==}
        case Some{x}:
          {==}

def CronJob.cron_take_starts_claim(p, c, j):
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match st:
        case Cr.Active{}:
          match nx:
            case None{}:
              cts.same(cl, CronJob.Rest{i, s, rs, ss, h})
            case Some{+n}:
              cts.due(Nat.is_le(n, c), p, c, i, s, n, k, cl, rs, ss, h)
        case Cr.Paused{}:
          cts.same(cl, CronJob.Rest{i, s, rs, ss, h})
        case Cr.Finished{}:
          cts.same(cl, CronJob.Rest{i, s, rs, ss, h})
        case Cr.Cancelled{}:
          cts.same(cl, CronJob.Rest{i, s, rs, ss, h})
