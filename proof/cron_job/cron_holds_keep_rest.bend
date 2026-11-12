# eukhe: the proof of LAW cron_holds_keep_rest
# A cancel, a pause and a stop: a case split on the status; a delete
# builds the job with the same rest. A recovery: a job with no claim
# stays; with a claim, by cases on the verdict, the status and, for an
# active job, whether it is a one-shot (a one-shot fired again has its
# starts withdrawn); the model's verdict is the spec's (LCj.cj.clears).

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron_job.bend as CronJob
import ./base.bend as LCj

def chk.cancel(j: Cr.Job) -> {CronJob.rest_spec(Cr.cancel(j)) == CronJob.rest_spec(j) : CronJob.Rest}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match st:
        case Cr.Active{}:
          {==}
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

def chk.pause(j: Cr.Job) -> {CronJob.rest_spec(Cr.pause(j)) == CronJob.rest_spec(j) : CronJob.Rest}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match st:
        case Cr.Active{}:
          {==}
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

def chk.stop(j: Cr.Job) -> {CronJob.rest_spec(Cr.stop(j)) == CronJob.rest_spec(j) : CronJob.Rest}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match st:
        case Cr.Active{}:
          {==}
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

def chk.delete(j: Cr.Job) -> {CronJob.rest_spec(Cr.delete(j)) == CronJob.rest_spec(j) : CronJob.Rest}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      {==}

# an active job whose claim is cleared: a one-shot fired again withdraws
# its starts, a repeating job keeps them
def chk.end(s: Cr.Sched, +i: Nat, +nx: Maybe<&2, Nat>, +k: Nat, x: Cr.Claim, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {CronJob.rest_spec(Cr.recover.end(Cr.is_once(s), i, s, nx, k, x, rs, ss, h)) == CronJob.withdrawn_spec(True{}, Cr.Active{}, s, CronJob.Rest{i, s, rs, ss, h}) : CronJob.Rest}:
  match s:
    case Cr.Once{d}:
      match x:
        case Cr.Claim{oc, o}:
          {==}
    case Cr.Every{n}:
      {==}

def chk.go(b: Bool, +i: Nat, +s: Cr.Sched, st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +x: Cr.Claim, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {CronJob.rest_spec(Cr.recover.go(b, i, s, st, nx, k, x, rs, ss, h)) == CronJob.withdrawn_spec(b, st, s, CronJob.Rest{i, s, rs, ss, h}) : CronJob.Rest}:
  match b:
    case False{}:
      {==}
    case True{}:
      match st:
        case Cr.Active{}:
          chk.end(s, i, nx, k, x, rs, ss, h)
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

def chk.recover(+p: Nat, +dead: List<&2, Nat>, j: Cr.Job) -> {CronJob.rest_spec(Cr.recover(p, dead, j)) == CronJob.recovered_spec(p, dead, j) : CronJob.Rest}:
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, cl, +rs, +ss, +h}:
      match cl:
        case None{}:
          {==}
        case Some{x}:
          match x:
            case Cr.Claim{+occ, +o}:
              Equal.trans(CronJob.Rest, CronJob.rest_spec(Cr.recover.go(Cr.clears(p, o, rs, dead), i, s, st, nx, k, Cr.Claim{occ, o}, rs, ss, h)), CronJob.withdrawn_spec(Cr.clears(p, o, rs, dead), st, s, CronJob.Rest{i, s, rs, ss, h}), CronJob.withdrawn_spec(CronJob.clears_spec(p, o, rs, dead), st, s, CronJob.Rest{i, s, rs, ss, h}), chk.go(Cr.clears(p, o, rs, dead), i, s, st, nx, k, Cr.Claim{occ, o}, rs, ss, h), Equal.cong(Bool, CronJob.Rest, z => CronJob.withdrawn_spec(z, st, s, CronJob.Rest{i, s, rs, ss, h}), Cr.clears(p, o, rs, dead), CronJob.clears_spec(p, o, rs, dead), LCj.cj.clears(p, o, rs, dead)))

def CronJob.cron_holds_keep_rest(p, dead, j):
  (chk.cancel(j), (chk.pause(j), (chk.stop(j), (chk.delete(j), chk.recover(p, dead, j)))))
