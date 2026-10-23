# eukhe: the proof of LAW facts_fit_ceiling_under_model

import Base
import ../../bend/facts.bend as Fx
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pf.fit_at_max(+m: Nat, +b: Nat, +a: Nat, c: Bool) -> {Fx.Fit.max(Fx.fit.at(c, m, b, a)) == m : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def pf.cap_le(+base: Maybe<&2, Nat>, +mm: Nat, +b: Nat) -> {Nat.is_le(Fx.fit.cap(base, mm, b), mm) == True{} : Bool}:
  match base:
    case None{}:
      LA.facts.pf.le_refl(mm)
    case Some{+x}:
      %Equal.sym(Nat, Fx.fit.cap(Some{x}, mm, b), Nat.min(Nat.add(x, b), mm), LA.w2.cap_sum(x, mm, b)) : {Nat.is_le(_, mm) == True{} : Bool}
      LA.pf.min_le_r(Nat.add(x, b), mm)

def pf.facts_fit_ceiling_under_model(+base: Maybe<&2, Nat>, +mm: Nat, +b: Nat, +a: Nat) -> {Nat.is_le(Fx.Fit.max(Fx.fit(base, mm, b, a)), mm) == True{} : Bool}:
  +m = Fx.fit.cap(base, mm, b)
  +c = Nat.is_le(m, b)
  %Equal.sym(Nat, Fx.Fit.max(Fx.fit.at(c, m, b, a)), m, pf.fit_at_max(m, b, a, c)) : {Nat.is_le(_, mm) == True{} : Bool}
  pf.cap_le(base, mm, b)

def Laws.facts_fit_ceiling_under_model(base, mm, b, a):
  pf.facts_fit_ceiling_under_model(base, mm, b, a)
