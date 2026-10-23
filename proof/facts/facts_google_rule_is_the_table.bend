# eukhe: the proof of LAW facts_google_rule_is_the_table

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts.bend as Facts
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

# a below b and b at most a cannot both hold
def pf.lt_le_absurd(-A: Type, +a: Nat, +b: Nat, h1: {Nat.is_lt(a, b) == True{} : Bool}, h2: {Nat.is_le(b, a) == True{} : Bool}) -> A:
  match a b:
    case 0n 0n:
      LLogicLogic.pq.absurdF(A, h1)
    case 0n 1n+q:
      LLogicLogic.pq.absurdF(A, h2)
    case 1n+p 0n:
      LLogicLogic.pq.absurdF(A, h1)
    case 1n+p 1n+q:
      pf.lt_le_absurd(A, p, q, h1, h2)

def pf.hi_id(+x: Nat, +hi: Nat, g: Bool, eg: {Nat.is_lt(hi, x) == g : Bool}, xhi: {Nat.is_le(x, hi) == True{} : Bool}) -> {Fx.clamp.hi(g, x, hi) == x : Nat}:
  match g:
    case True{}:
      pf.lt_le_absurd({hi == x : Nat}, hi, x, eg, xhi)
    case False{}:
      {==}

def pf.lo_id(+x: Nat, +lo: Nat, +hi: Nat, c: Bool, ec: {Nat.is_lt(x, lo) == c : Bool}, lox: {Nat.is_le(lo, x) == True{} : Bool}, xhi: {Nat.is_le(x, hi) == True{} : Bool}) -> {Fx.clamp.lo(c, x, lo, hi) == x : Nat}:
  match c:
    case True{}:
      pf.lt_le_absurd({lo == x : Nat}, x, lo, ec, lox)
    case False{}:
      pf.hi_id(x, hi, Nat.is_lt(hi, x), {==}, xhi)

# a value inside lo..hi stays as it is
def pf.clamp_id(+x: Nat, +lo: Nat, +hi: Nat, lox: {Nat.is_le(lo, x) == True{} : Bool}, xhi: {Nat.is_le(x, hi) == True{} : Bool}) -> {Fx.clamp(x, lo, hi) == x : Nat}:
  pf.lo_id(x, lo, hi, Nat.is_lt(x, lo), {==}, lox, xhi)

def pf.table_at(+mi: Nat, +lo: Nat, +me: Nat, +hi: Nat, l: Fx.Lv, ml: {Nat.is_le(mi, lo) == True{} : Bool}, lm: {Nat.is_le(lo, me) == True{} : Bool}, mh: {Nat.is_le(me, hi) == True{} : Bool}) -> {Fx.gtokens(Fx.Budgets{mi, lo, me, hi}, Fx.Customs.none(), l) == Fx.Budgets.at(Fx.Budgets{mi, lo, me, hi}, l) : Nat}:
  match l:
    case Fx.Minimal{}:
      pf.clamp_id(mi, mi, hi, LA.facts.pf.le_refl(mi), LA.pf.le_trans(mi, lo, hi, ml, LA.pf.le_trans(lo, me, hi, lm, mh)))
    case Fx.Low{}:
      pf.clamp_id(lo, mi, hi, ml, LA.pf.le_trans(lo, me, hi, lm, mh))
    case Fx.Medium{}:
      pf.clamp_id(me, mi, hi, LA.pf.le_trans(mi, lo, me, ml, lm), mh)
    case Fx.High{}:
      pf.clamp_id(hi, mi, hi, LA.pf.le_trans(mi, lo, hi, ml, LA.pf.le_trans(lo, me, hi, lm, mh)), LA.facts.pf.le_refl(hi))

def pf.facts_google_rule_is_the_table(+b: Fx.Budgets, +l: Fx.Lv, +ordered: {Fx.Budgets.ordered(b) == True{} : Bool}) -> {Fx.gtokens(b, Fx.Customs.none(), l) == Fx.Budgets.at(b, l) : Nat}:
  match b:
    case Fx.Budgets{+mi, +lo, +me, +hi}:
      +rest = LLogicBool.pq.and_r(Nat.is_le(mi, lo), Bool.and(Nat.is_le(lo, me), Nat.is_le(me, hi)), ordered)
      pf.table_at(mi, lo, me, hi, l, LLogicBool.pq.and_l(Nat.is_le(mi, lo), Bool.and(Nat.is_le(lo, me), Nat.is_le(me, hi)), ordered), LLogicBool.pq.and_l(Nat.is_le(lo, me), Nat.is_le(me, hi), rest), LLogicBool.pq.and_r(Nat.is_le(lo, me), Nat.is_le(me, hi), rest))

def Facts.facts_google_rule_is_the_table(b, l, ordered):
  pf.facts_google_rule_is_the_table(b, l, ordered)
