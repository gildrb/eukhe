# eukhe: the proof of LAW limits_plan_wraps_first
#
# PROOF: the code counts the place up as it goes, the spec adds one on the way back: equal from any start (lw.go).

import Base
import ../../bend/budget.bend as B
import ../../bend/limits.bend as L
import ../../laws/limits.bend as Limits
import ../../spec/budget/limits.bend as S
import ./base.bend as LB

# a place found after the first i windows is i on
def lw.addm(i: Nat, m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{j}:
      Some{Nat.add(i, j)}

def lw.step(b: Bool, +i: Nat, m: Maybe<&2, Nat>) -> {L.wraps.at(b, i, lw.addm(1n+i, m)) == lw.addm(i, S.over.at(b, m)) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      %LB.lmb.add_zero(i) : {Some{_} == Some{Nat.add(i, 0n)} : Maybe<&2, Nat>}
      {==}
    case False{}:
      match m:
        case None{}:
          {==}
        case Some{j}:
          %LB.lmb.add_succ(i, j) : {Some{_} == Some{Nat.add(i, 1n+j)} : Maybe<&2, Nat>}
          {==}

def lw.go(us: List<&2, Nat>, +line: Nat, +i: Nat) -> {L.wraps.go(us, line, i) == lw.addm(i, S.over(us, line)) : Maybe<&2, Nat>}:
  match us:
    case Nil{}:
      {==}
    case Con{+u, +t}:
      %Equal.sym(Maybe<&2, Nat>, L.wraps.go(t, line, 1n+i), lw.addm(1n+i, S.over(t, line)), lw.go(t, line, 1n+i)) : {L.wraps.at(Nat.is_le(line, u), i, _) == lw.addm(i, S.over.at(Nat.is_le(line, u), S.over(t, line))) : Maybe<&2, Nat>}
      lw.step(Nat.is_le(line, u), i, S.over(t, line))

def lw.zero(m: Maybe<&2, Nat>) -> {lw.addm(0n, m) == m : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{j}:
      {==}

def Limits.limits_plan_wraps_first(us, r):
  Equal.trans(Maybe<&2, Nat>, L.wraps.go(us, Nat.sub(1000n, r), 0n), lw.addm(0n, S.over(us, Nat.sub(1000n, r))), S.over(us, Nat.sub(1000n, r)), lw.go(us, Nat.sub(1000n, r), 0n), lw.zero(S.over(us, Nat.sub(1000n, r))))
