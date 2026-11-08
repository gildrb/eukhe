# eukhe: the proof of LAW facts_fit_ceiling_under_model

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts
import ./base.bend as LA

def pf.cap_le(+base: Maybe<&2, Nat>, +mm: Nat, +b: Nat) -> {Nat.is_le(Fx.fit.cap(base, mm, b), mm) == True{} : Bool}:
  match base:
    case None{}:
      LA.facts.pf.le_refl(mm)
    case Some{+x}:
      %Equal.sym(Nat, Fx.fit.cap(Some{x}, mm, b), Nat.min(Nat.add(x, b), mm), LA.w2.cap_sum(x, mm, b)) : {Nat.is_le(_, mm) == True{} : Bool}
      LA.pf.min_le_r(Nat.add(x, b), mm)

def Facts.facts_fit_ceiling_under_model(base, mm, b, a, w, p, s, f, st, hf):
  +k = Fx.fit.cap(base, mm, b)
  LA.pf.le_trans(Fx.cap.shrink(k, Fx.Win{w, p, s, f, st}), Nat.max(f, k), mm, LA.pf.shrink_le(k, w, p, s, f, st), LA.pf.max_le(f, k, mm, hf, pf.cap_le(base, mm, b)))
