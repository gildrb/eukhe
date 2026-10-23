# eukhe: the proof of LAW goal_judge_is_check

import Base
import ../../bend/progress.bend as Pr
import ../../laws/progress.bend as Progress
import ../base.bend as L
import ./base.bend as LA

# 1 + s <= t when s < t
def pp.lt_le_succ(s: Nat, t: Nat, h: {Nat.is_lt(s, t) == True{} : Bool}) -> {Nat.is_le(1n+s, t) == True{} : Bool}:
  %LA.pp.lt_is_le(s, t) : {_ == True{} : Bool}
  h

# s <= t - 1 when s < t
def pp.lt_pred(s: Nat, t: Nat, h: {Nat.is_lt(s, t) == True{} : Bool}) -> {Nat.is_le(s, Nat.sub(t, 1n)) == True{} : Bool}:
  match s t:
    case 0n 0n:
      L.pj.absurdF({Nat.is_le(0n, Nat.sub(0n, 1n)) == True{} : Bool}, h)
    case 0n 1n+tp:
      L.pj.le0(Nat.sub(1n+tp, 1n))
    case 1n+sp 0n:
      L.pj.absurdF({Nat.is_le(1n+sp, Nat.sub(0n, 1n)) == True{} : Bool}, h)
    case 1n+sp 1n++tp:
      %L.pj.sub_zero(tp) : {Nat.is_le(1n+sp, _) == True{} : Bool}
      pp.lt_le_succ(sp, tp, h)

def pp.judge_is_check(+t: Nat, +cap: Nat, +s: Nat, +w: Nat, +work: Nat, below: {Nat.is_lt(s, t) == True{} : Bool}) -> {Pr.judge(t, cap, Some{Pr.Prior{s, w}}, work) == Pr.check(cap, s, Nat.is_lt(w, work)) : Pr.Goal}:
  %L.pj.min_of_le(s, Nat.sub(t, 1n), pp.lt_pred(s, t, below)) : {Pr.check(cap, _, Nat.is_lt(w, work)) == Pr.check(cap, s, Nat.is_lt(w, work)) : Pr.Goal}
  {==}

def Progress.goal_judge_is_check(t, cap, s, w, work, below):
  pp.judge_is_check(t, cap, s, w, work, below)
