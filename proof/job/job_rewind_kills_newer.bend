# eukhe: the proof of LAW job_rewind_kills_newer
# A commit at or past t is not below t, so the tree at t does not hold
# the job.

import Base
import ../../bend/job.bend as Jb
import ../../laws/job.bend as Job
import ../base/logic/logic.bend as LLogicLogic

def rk.le_nlt(t: Nat, a: Nat, h: {Nat.is_le(t, a) == True{} : Bool}) -> {False{} == Nat.is_lt(a, t) : Bool}:
  match t a:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LLogicLogic.pj.absurdF({False{} == Nat.is_lt(0n, 1n+p) : Bool}, h)
    case 1n+p 1n+q:
      rk.le_nlt(p, q, h)

def Job.job_rewind_kills_newer(t, a, after):
  %rk.le_nlt(t, a, after) : {[Bool.not(_)] == [True{}] : List<&2, Bool>}
  {==}
