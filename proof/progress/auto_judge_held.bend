# eukhe: the proof of LAW auto_judge_held

import Base
import ../../bend/progress.bend as Pr
import ../../laws/progress.bend as Progress
import ../base/nat.bend as LNat

def pp.go_stalls(steer: Bool, +n: Nat) -> {n == Pr.Run.stalls(Pr.strike.go(steer, n)) : Nat}:
  match steer:
    case True{}:
      {==}
    case False{}:
      {==}

def pp.strike_stalls(b: Bool, steer: Bool, +n: Nat) -> {n == Pr.Run.stalls(Pr.strike.put(b, steer, n)) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      pp.go_stalls(steer, n)

def pp.held_check(+u: Nat, +cap: Nat, +m: Nat, g: Bool, h: {Nat.is_le(m, u) == True{} : Bool}) -> {Nat.is_le(Pr.Run.stalls(Pr.check(cap, m, g)), 1n+u) == True{} : Bool}:
  match g:
    case True{}:
      {==}
    case False{}:
      %pp.strike_stalls(Nat.is_le(Nat.add(cap, cap), 1n+m), Nat.is_eq(cap, 1n+m), 1n+m) : {Nat.is_le(_, 1n+u) == True{} : Bool}
      h

def pp.judge_held(+u: Nat, +cap: Nat, p: Maybe<&2, Pr.Prior>, +work: Nat) -> {Nat.is_le(Pr.Run.stalls(Pr.judge(1n+u, cap, p, work)), 1n+u) == True{} : Bool}:
  match p:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case Pr.Prior{+s, +w}:
          %LNat.pj.sub_zero(u) : {Nat.is_le(Pr.Run.stalls(Pr.check(cap, Nat.min(s, _), Nat.is_lt(w, work))), 1n+u) == True{} : Bool}
          pp.held_check(u, cap, Nat.min(s, u), Nat.is_lt(w, work), LNat.pj.min_le_r(s, u))

def Progress.auto_judge_held(u, cap, p, work):
  pp.judge_held(u, cap, p, work)
