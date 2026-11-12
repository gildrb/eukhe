# eukhe: the proof of LAW facts_aux_keeps_answer_room
#
# PROOF: the code's sum-avoiding cap is min(B + a, top) (the lemmas of
# facts_aux_cap_within), which is B + a when that sum is at most top.

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA
import ./facts_aux_cap_within.bend as PAux

def ak.main(+c: Fx.Customs, +d: Fx.Budgets, +a: Nat, +top: Nat, +fits: {Nat.is_le(Nat.add(Fx.budget(c, d, Fx.High{}), a), top) == True{} : Bool}) -> {Fx.aux(c, d, a, top) == Nat.add(Fx.budget(c, d, Fx.High{}), a) : Nat}:
  +B = Fx.budget(c, d, Fx.High{})
  +C = Nat.is_lt(B, Nat.sub(top, a))
  +w = Equal.trans(Nat, Fx.aux_cap.add(C, B, a, top), Fx.fit.cap.add(C, a, top, B), Nat.min(Nat.add(B, a), top), PAux.w2.aux_cap(C, B, a, top), PAux.w2.aux_sum(B, a, top))
  Equal.trans(Nat, Fx.aux_cap.add(C, B, a, top), Nat.min(Nat.add(B, a), top), Nat.add(B, a), w, Equal.sym(Nat, Nat.add(B, a), Nat.min(Nat.add(B, a), top), LNat.pj.min_of_le(Nat.add(B, a), top, fits)))

def Facts.facts_aux_keeps_answer_room(c, d, a, top, fits):
  ak.main(c, d, a, top, fits)
