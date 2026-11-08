# eukhe: the proof of LAW cron_recover_job_exact
# A job with no claim stays on both sides. A claim of o: the model's verdict
# Cr.clears is the spec's clears_spec (membership, LCj.cj.has); then by
# cases on the verdict, the status and, for an active job, the schedule.

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron_job.bend as CronJob
import ../../laws/cron_terms.bend as CronTerms
import ./base.bend as LCj

def cjr.clears(+p: Nat, +o: Nat, +rs: List<&2, Nat>, +dead: List<&2, Nat>) -> {Cr.clears(p, o, rs, dead) == CronJob.clears_spec(p, o, rs, dead) : Bool}:
  %LCj.cj.has(p, rs) : {Bool.or(Bool.and(Nat.is_eq(o, p), Bool.not(Cr.has(p, rs))), Cr.has(o, dead)) == Bool.or(Bool.and(Nat.is_eq(o, p), Bool.not(_)), CronTerms.has_spec(o, dead)) : Bool}
  %LCj.cj.has(o, dead) : {Bool.or(Bool.and(Nat.is_eq(o, p), Bool.not(Cr.has(p, rs))), Cr.has(o, dead)) == Bool.or(Bool.and(Nat.is_eq(o, p), Bool.not(Cr.has(p, rs))), _) : Bool}
  {==}

def cjr.ended(s: Cr.Sched, +i: Nat, +nx: Maybe<&2, Nat>, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {Cr.recover.end(Cr.is_once(s), i, s, nx, k, rs, ss, h) == CronJob.ended_spec(s, i, nx, k, rs, ss, h) : Cr.Job}:
  match s:
    case Cr.Once{d}:
      {==}
    case Cr.Every{n}:
      {==}

def cjr.go(b: Bool, +i: Nat, +s: Cr.Sched, st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +x: Cr.Claim, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {Cr.recover.go(b, i, s, st, nx, k, x, rs, ss, h) == CronJob.recover_go_spec(b, i, s, st, nx, k, x, rs, ss, h) : Cr.Job}:
  match b:
    case False{}:
      {==}
    case True{}:
      match st:
        case Cr.Active{}:
          cjr.ended(s, i, nx, k, rs, ss, h)
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

def CronJob.cron_recover_job_exact(p, dead, j):
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, cl, +rs, +ss, +h}:
      match cl:
        case None{}:
          {==}
        case Some{x}:
          match x:
            case Cr.Claim{+occ, +o}:
              %cjr.clears(p, o, rs, dead) : {Cr.recover.go(Cr.clears(p, o, rs, dead), i, s, st, nx, k, Cr.Claim{occ, o}, rs, ss, h) == CronJob.recover_go_spec(_, i, s, st, nx, k, Cr.Claim{occ, o}, rs, ss, h) : Cr.Job}
              cjr.go(Cr.clears(p, o, rs, dead), i, s, st, nx, k, Cr.Claim{occ, o}, rs, ss, h)
