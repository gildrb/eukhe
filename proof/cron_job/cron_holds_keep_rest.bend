# eukhe: the proof of LAW cron_holds_keep_rest
# A cancel, a pause and a stop: a case split on the status; a delete
# builds the job with the same rest. A recovery: a job with no claim
# stays; with a claim, by cases on the verdict, the status and, for an
# active job, whether it is a one-shot.

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron_job.bend as CronJob

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

def chk.end(b: Bool, +i: Nat, +s: Cr.Sched, +nx: Maybe<&2, Nat>, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {CronJob.rest_spec(Cr.recover.end(b, i, s, nx, k, rs, ss, h)) == CronJob.Rest{i, s, rs, ss, h} : CronJob.Rest}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def chk.go(b: Bool, +i: Nat, +s: Cr.Sched, st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +x: Cr.Claim, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {CronJob.rest_spec(Cr.recover.go(b, i, s, st, nx, k, x, rs, ss, h)) == CronJob.Rest{i, s, rs, ss, h} : CronJob.Rest}:
  match b:
    case False{}:
      {==}
    case True{}:
      match st:
        case Cr.Active{}:
          chk.end(Cr.is_once(s), i, s, nx, k, rs, ss, h)
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

def chk.recover(+p: Nat, +dead: List<&2, Nat>, j: Cr.Job) -> {CronJob.rest_spec(Cr.recover(p, dead, j)) == CronJob.rest_spec(j) : CronJob.Rest}:
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, cl, +rs, +ss, +h}:
      match cl:
        case None{}:
          {==}
        case Some{x}:
          match x:
            case Cr.Claim{+occ, +o}:
              chk.go(Cr.clears(p, o, rs, dead), i, s, st, nx, k, Cr.Claim{occ, o}, rs, ss, h)

def CronJob.cron_holds_keep_rest(p, dead, j):
  (chk.cancel(j), (chk.pause(j), (chk.stop(j), (chk.delete(j), chk.recover(p, dead, j)))))
