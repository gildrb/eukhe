# eukhe: the proof of LAW job_output_bounded

import Base
import ../../bend/job.bend as Jb
import ../../laws/job.bend as Job
import ../base.bend as L

# a kept count under the cap stays under it after any output
def pj.bound(k: Nat, c: Nat, +n: Nat, h: {Nat.is_le(k, c) == True{} : Bool}) -> {Nat.is_le(Nat.add(k, Nat.min(n, Nat.sub(c, k))), c) == True{} : Bool}:
  match k c:
    case 0n 0n:
      L.pj.min_le_r(n, 0n)
    case 0n 1n+cp:
      L.pj.min_le_r(n, 1n+cp)
    case 1n+kp 0n:
      L.pj.absurdF({Nat.is_le(Nat.add(1n+kp, Nat.min(n, Nat.sub(0n, 1n+kp))), 0n) == True{} : Bool}, h)
    case 1n+kp 1n+cp:
      pj.bound(kp, cp, n, h)

# one step keeps the kept bytes under the cap
def pj.step_bd(+c: Nat, j: Jb.J, e: Jb.JEv, h: {Nat.is_le(Jb.J.kept(j), c) == True{} : Bool}) -> {Nat.is_le(Jb.J.kept(Jb.step(Some{c}, j, e)), c) == True{} : Bool}:
  match j:
    case Jb.Live{+k, d}:
      match e:
        case Jb.Out{+n}:
          pj.bound(k, c, n, h)
        case Jb.Quit{q}:
          h
        case Jb.Kill{}:
          h
        case Jb.Tick{}:
          h
    case Jb.Ended{k, d, x}:
      h

def pj.bounded(es: List<&2, Jb.JEv>, +c: Nat, +j: Jb.J, h: {Nat.is_le(Jb.J.kept(j), c) == True{} : Bool}) -> {Nat.is_le(Jb.J.kept(Jb.go(es, Some{c}, j)), c) == True{} : Bool}:
  match es:
    case Nil{}:
      h
    case +e <> rest:
      pj.bounded(rest, c, Jb.step(Some{c}, j, e), pj.step_bd(c, j, e, h))

# The laws
# --------

def pj.job_output_bounded(+c: Nat, es: List<&2, Jb.JEv>) -> {Nat.is_le(Jb.J.kept(Jb.run(Some{c}, es)), c) == True{} : Bool}:
  pj.bounded(es, c, Jb.Live{0n, 0n}, L.pj.le0(c))

# (S2) Jobs and limits

def Job.job_output_bounded(c, es):
  pj.job_output_bounded(c, es)
