# eukhe: the proof of LAW job_feed_bounded

import Base
import ../../bend/job.bend as Jb
import ../../laws/job.bend as Job
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

# a + m <= t when a <= t and m <= t - a
def pj.add_le_sub(a: Nat, t: Nat, +m: Nat, ha: {Nat.is_le(a, t) == True{} : Bool}, hm: {Nat.is_le(m, Nat.sub(t, a)) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, m), t) == True{} : Bool}:
  match a t:
    case 0n 0n:
      hm
    case 0n 1n+tp:
      hm
    case 1n+ap 0n:
      LLogicLogic.pj.absurdF({Nat.is_le(Nat.add(1n+ap, m), 0n) == True{} : Bool}, ha)
    case 1n+ap 1n+tp:
      pj.add_le_sub(ap, tp, m, ha, hm)

def pj.job_feed_bounded(+t: Nat, +cap: Maybe<&2, Nat>, +j: Jb.J, e: Jb.JEv, below: {Nat.is_le(Jb.J.total(j), t) == True{} : Bool}) -> {Nat.is_le(Jb.J.total(Jb.feed(t, cap, j, e)), t) == True{} : Bool}:
  match j:
    case Jb.Live{+k, +d}:
      match e:
        case Jb.Out{+n}:
          %LA.pj.out_total(cap, k, d, Nat.min(n, Nat.sub(Nat.sub(t, k), d))) : {Nat.is_le(_, t) == True{} : Bool}
          %LA.pj.sub_sub_r(t, k, d) : {Nat.is_le(Nat.add(Nat.add(k, d), Nat.min(n, _)), t) == True{} : Bool}
          pj.add_le_sub(Nat.add(k, d), t, Nat.min(n, Nat.sub(t, Nat.add(k, d))), below, LNat.pj.min_le_r(n, Nat.sub(t, Nat.add(k, d))))
        case Jb.Quit{c}:
          below
        case Jb.Kill{}:
          below
        case Jb.Tick{}:
          below
    case Jb.Ended{k, d, x}:
      below

def Job.job_feed_bounded(t, cap, j, e, below):
  pj.job_feed_bounded(t, cap, j, e, below)
