# eukhe: the proof of LAW facts_fit_ceiling_is_the_cap
#
# PROOF: without a caller's cap both sides shrink mm through the window;
# with one, the code's sum-avoiding ceiling is min(x + b, mm)
# (LA.w2.cap_sum), which the cap shrinks the same way.

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

def fc.main(+base: Maybe<&2, Nat>, +mm: Nat, +b: Nat, +a: Nat, +win: Fx.Win) -> {Some{Fx.Fit.max(Fx.fit(base, mm, b, a, win))} == Fx.cap(Facts.fit_caller(base, mm, b), mm, True{}, win) : Maybe<&2, Nat>}:
  match base:
    case None{}:
      {==}
    case Some{x}:
      %Equal.sym(Nat, Fx.fit.cap(Some{x}, mm, b), Nat.min(Nat.add(x, b), mm), LA.w2.cap_sum(x, mm, b)) : {Some{Fx.cap.shrink(_, win)} == Some{Fx.cap.shrink(Nat.min(Nat.add(x, b), mm), win)} : Maybe<&2, Nat>}
      {==}

def Facts.facts_fit_ceiling_is_the_cap(base, mm, b, a, win):
  fc.main(base, mm, b, a, win)
