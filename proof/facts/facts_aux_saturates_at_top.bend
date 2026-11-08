# eukhe: the proof of LAW facts_aux_saturates_at_top
#
# PROOF: the code's sum-avoiding cap is min(B + a, top) (the lemmas of
# facts_aux_cap_within), which is top when the sum passes it.

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA
import ./facts_aux_cap_within.bend as PAux

def sa.main(+c: Fx.Customs, +d: Fx.Budgets, +a: Nat, +top: Nat, +past: {Nat.is_lt(top, Nat.add(Fx.budget(c, d, Fx.High{}), a)) == True{} : Bool}) -> {Fx.aux(c, d, a, top) == top : Nat}:
  +B = Fx.budget(c, d, Fx.High{})
  +C = Nat.is_lt(B, Nat.sub(top, a))
  +w = Equal.trans(Nat, Fx.aux_cap.add(C, B, a, top), Fx.fit.cap.add(C, a, top, B), Nat.min(Nat.add(B, a), top), PAux.w2.aux_cap(C, B, a, top), PAux.w2.aux_sum(B, a, top))
  Equal.trans(Nat, Fx.aux_cap.add(C, B, a, top), Nat.min(Nat.add(B, a), top), top, w, LA.w2.min_r(Nat.add(B, a), top, LNat.pc.lt_to_le(top, Nat.add(B, a), past)))

def Facts.facts_aux_saturates_at_top(c, d, a, top, past):
  sa.main(c, d, a, top, past)
