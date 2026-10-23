# eukhe: the proof of LAW goal_judge_top_stops

import Base
import ../../bend/progress.bend as Pr
import ../../laws/progress.bend as Progress
import ../base.bend as L

# min(1 + u, u) == u
def pp.min_succ(u: Nat) -> {u == Nat.min(1n+u, u) : Nat}:
  match u:
    case 0n:
      {==}
    case 1n+p:
      %pp.min_succ(p) : {1n+p == 1n+_ : Nat}
      {==}

def pp.judge_top_stops(+u: Nat, +cap: Nat, +w: Nat, +work: Nat, fits: {Nat.is_le(cap, 1n+u) == True{} : Bool}, same: {Nat.is_lt(w, work) == False{} : Bool}) -> {Pr.judge(1n+u, cap, Some{Pr.Prior{1n+u, w}}, work) == Pr.Stop{1n+u} : Pr.Goal}:
  %L.pj.sub_zero(u) : {Pr.check(cap, Nat.min(1n+u, _), Nat.is_lt(w, work)) == Pr.Stop{1n+u} : Pr.Goal}
  %pp.min_succ(u) : {Pr.check(cap, _, Nat.is_lt(w, work)) == Pr.Stop{1n+u} : Pr.Goal}
  %Equal.sym(Bool, Nat.is_lt(w, work), False{}, same) : {Pr.check(cap, u, _) == Pr.Stop{1n+u} : Pr.Goal}
  %Equal.sym(Bool, Nat.is_le(cap, 1n+u), True{}, fits) : {Pr.strike.put(_, 1n+u) == Pr.Stop{1n+u} : Pr.Goal}
  {==}

def Progress.goal_judge_top_stops(u, cap, w, work, fits, same):
  pp.judge_top_stops(u, cap, w, work, fits, same)
