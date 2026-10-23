# eukhe: the proof of LAW facts_google_budget_at_most_high

import Base
import ../../bend/facts.bend as Fx
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pf.hi_le(+x: Nat, +hi: Nat, g: Bool, eg: {Nat.is_lt(hi, x) == g : Bool}) -> {Nat.is_le(Fx.clamp.hi(g, x, hi), hi) == True{} : Bool}:
  match g:
    case True{}:
      LA.facts.pf.le_refl(hi)
    case False{}:
      LA.pf.not_lt_le(hi, x, eg)

def pf.lo_le(+x: Nat, +lo: Nat, +hi: Nat, c: Bool, lohi: {Nat.is_le(lo, hi) == True{} : Bool}) -> {Nat.is_le(Fx.clamp.lo(c, x, lo, hi), hi) == True{} : Bool}:
  match c:
    case True{}:
      lohi
    case False{}:
      pf.hi_le(x, hi, Nat.is_lt(hi, x), {==})

def pf.clamp_le(+x: Nat, +lo: Nat, +hi: Nat, lohi: {Nat.is_le(lo, hi) == True{} : Bool}) -> {Nat.is_le(Fx.clamp(x, lo, hi), hi) == True{} : Bool}:
  pf.lo_le(x, lo, hi, Nat.is_lt(x, lo), lohi)

def pf.facts_google_budget_at_most_high(+b: Fx.Budgets, c: Fx.Customs, +l: Fx.Lv, +ordered: {Fx.Budgets.ordered(b) == True{} : Bool}) -> {Nat.is_le(Fx.gtokens(b, c, l), Fx.Budgets.high(b)) == True{} : Bool}:
  pf.clamp_le(Maybe.default(&2, Nat, Fx.Customs.at(c, l), Fx.Budgets.at(b, l)), Fx.Budgets.minimal(b), Fx.Budgets.high(b), LA.pf.ord_mh(b, ordered))

def Laws.facts_google_budget_at_most_high(b, c, l, ordered):
  pf.facts_google_budget_at_most_high(b, c, l, ordered)
