# eukhe: the proof of LAW job_rewind_exact
# Job by job: the model's held is the laws' held (a commit below the
# target is one the target is not at or below), so each kill is the spec's.

import Base
import ../../bend/job.bend as Jb
import ../../laws/job.bend as Job

def pr.not_le(t: Nat, a: Nat) -> {Nat.is_lt(a, t) == Bool.not(Nat.is_le(t, a)) : Bool}:
  match t a:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pr.not_le(p, q)

def pr.held(target: Maybe<&2, Nat>, a: Maybe<&2, Nat>) -> {Jb.held(target, a) == Job.rw_held_spec(target, a) : Bool}:
  match target a:
    case None{} None{}:
      {==}
    case None{} Some{x}:
      {==}
    case Some{t} None{}:
      {==}
    case Some{t} Some{x}:
      pr.not_le(t, x)

def pr.kill(+target: Maybe<&2, Nat>, s: Jb.Seen) -> {Jb.kill.of(target, s) == Job.rw_kill_spec(target, s) : Bool}:
  match s:
    case Jb.Seen{r, +a}:
      match r:
        case True{}:
          %pr.held(target, a) : {Bool.not(Jb.held(target, a)) == Bool.not(_) : Bool}
          {==}
        case False{}:
          {==}

def pr.kills(js: List<&2, Jb.Seen>, +target: Maybe<&2, Nat>) -> {Jb.kills(js, target) == Job.rw_kills_spec(js, target) : List<&2, Bool>}:
  match js:
    case Nil{}:
      {==}
    case +s <> +rest:
      %pr.kill(target, s) : {Jb.kill.of(target, s) <> Jb.kills(rest, target) == _ <> Job.rw_kills_spec(rest, target) : List<&2, Bool>}
      %pr.kills(rest, target) : {Jb.kill.of(target, s) <> Jb.kills(rest, target) == Jb.kill.of(target, s) <> _ : List<&2, Bool>}
      {==}

def Job.job_rewind_exact(js, target):
  pr.kills(js, target)
