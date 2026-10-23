# eukhe: the proof of LAW facts_google_budget_at_least_minimal

import Base
import ../../bend/facts.bend as Fx
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pf.hi_ge(+x: Nat, +lo: Nat, +hi: Nat, g: Bool, lohi: {Nat.is_le(lo, hi) == True{} : Bool}, lox: {Nat.is_le(lo, x) == True{} : Bool}) -> {Nat.is_le(lo, Fx.clamp.hi(g, x, hi)) == True{} : Bool}:
  match g:
    case True{}:
      lohi
    case False{}:
      lox

def pf.lo_ge(+x: Nat, +lo: Nat, +hi: Nat, c: Bool, ec: {Nat.is_lt(x, lo) == c : Bool}, lohi: {Nat.is_le(lo, hi) == True{} : Bool}) -> {Nat.is_le(lo, Fx.clamp.lo(c, x, lo, hi)) == True{} : Bool}:
  match c:
    case True{}:
      LA.facts.pf.le_refl(lo)
    case False{}:
      pf.hi_ge(x, lo, hi, Nat.is_lt(hi, x), lohi, LA.pf.not_lt_le(x, lo, ec))

def pf.clamp_ge(+x: Nat, +lo: Nat, +hi: Nat, lohi: {Nat.is_le(lo, hi) == True{} : Bool}) -> {Nat.is_le(lo, Fx.clamp(x, lo, hi)) == True{} : Bool}:
  pf.lo_ge(x, lo, hi, Nat.is_lt(x, lo), {==}, lohi)

def pf.facts_google_budget_at_least_minimal(+b: Fx.Budgets, c: Fx.Customs, +l: Fx.Lv, +ordered: {Fx.Budgets.ordered(b) == True{} : Bool}) -> {Nat.is_le(Fx.Budgets.minimal(b), Fx.gtokens(b, c, l)) == True{} : Bool}:
  pf.clamp_ge(Maybe.default(&2, Nat, Fx.Customs.at(c, l), Fx.Budgets.at(b, l)), Fx.Budgets.minimal(b), Fx.Budgets.high(b), LA.pf.ord_mh(b, ordered))

def Laws.facts_google_budget_at_least_minimal(b, c, l, ordered):
  pf.facts_google_budget_at_least_minimal(b, c, l, ordered)
