# eukhe: the proof of LAW job_rewind_kills_per_job
# Induction on the first table: each job gets its own kill, in place.

import Base
import ../../bend/job.bend as Jb
import ../../laws/job.bend as Job

def rk.app(xs: List<&2, Jb.Seen>, +ys: List<&2, Jb.Seen>, +target: Maybe<&2, Nat>) -> {Jb.kills(List.append(&2, Jb.Seen, xs, ys), target) == List.append(&2, Bool, Jb.kills(xs, target), Jb.kills(ys, target)) : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case +s <> rest:
      %rk.app(rest, ys, target) : {Jb.kill.of(target, s) <> Jb.kills(List.append(&2, Jb.Seen, rest, ys), target) == Jb.kill.of(target, s) <> _ : List<&2, Bool>}
      {==}

def Job.job_rewind_kills_per_job(xs, ys, target):
  rk.app(xs, ys, target)
