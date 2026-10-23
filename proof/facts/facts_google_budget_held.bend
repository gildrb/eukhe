# eukhe: the proof of LAW facts_google_budget_held

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts.bend as Facts
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

def w2.cong1(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  %e : {1n+a == 1n+_ : Nat}
  {==}

def w2.max_l(+a: Nat, +y: Nat, h: {Nat.is_le(y, a) == True{} : Bool}) -> {Nat.max(a, y) == a : Nat}:
  match a y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LLogicLogic.pq.absurdF({1n+q == 0n : Nat}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      w2.cong1(Nat.max(p, q), p, w2.max_l(p, q, h))

def w2.max_r(+a: Nat, +y: Nat, h: {Nat.is_le(a, y) == True{} : Bool}) -> {Nat.max(a, y) == y : Nat}:
  match a y:
    case 0n y:
      {==}
    case 1n+p 0n:
      LLogicLogic.pq.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      w2.cong1(Nat.max(p, q), q, w2.max_r(p, q, h))

def w2.min_l(+x: Nat, +y: Nat, h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.min(x, y) == x : Nat}:
  match x y:
    case 0n y:
      {==}
    case 1n+p 0n:
      LLogicLogic.pq.absurdF({0n == 1n+p : Nat}, h)
    case 1n+p 1n+q:
      w2.cong1(Nat.min(p, q), p, w2.min_l(p, q, h))

def w2.min_le_l(+x: Nat, +y: Nat) -> {Nat.is_le(Nat.min(x, y), x) == True{} : Bool}:
  match x y:
    case 0n y:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      w2.min_le_l(p, q)

def w2.lt_le(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n b:
      LNat.pq.le0(b)
    case 1n+p 0n:
      LLogicLogic.pq.absurdF({False{} == True{} : Bool}, h)
    case 1n+p 1n+q:
      w2.lt_le(p, q, h)

# x held inside lo..hi by the clamp is max(lo, min(x, hi))
def w2.held_hi(+x: Nat, +lo: Nat, +hi: Nat, g: Bool, eg: {Nat.is_lt(hi, x) == g : Bool}, lohi: {Nat.is_le(lo, hi) == True{} : Bool}, lox: {Nat.is_le(lo, x) == True{} : Bool}) -> {Fx.clamp.hi(g, x, hi) == Nat.max(lo, Nat.min(x, hi)) : Nat}:
  match g:
    case True{}:
      %Equal.sym(Nat, Nat.min(x, hi), hi, LA.w2.min_r(x, hi, w2.lt_le(hi, x, eg))) : {hi == Nat.max(lo, _) : Nat}
      Equal.sym(Nat, Nat.max(lo, hi), hi, w2.max_r(lo, hi, lohi))
    case False{}:
      %Equal.sym(Nat, Nat.min(x, hi), x, w2.min_l(x, hi, LA.pf.not_lt_le(hi, x, eg))) : {x == Nat.max(lo, _) : Nat}
      Equal.sym(Nat, Nat.max(lo, x), x, w2.max_r(lo, x, lox))

def w2.held_lo(+x: Nat, +lo: Nat, +hi: Nat, c: Bool, ec: {Nat.is_lt(x, lo) == c : Bool}, lohi: {Nat.is_le(lo, hi) == True{} : Bool}) -> {Fx.clamp.lo(c, x, lo, hi) == Nat.max(lo, Nat.min(x, hi)) : Nat}:
  match c:
    case True{}:
      +le = LA.pf.le_trans(Nat.min(x, hi), x, lo, w2.min_le_l(x, hi), w2.lt_le(x, lo, ec))
      Equal.sym(Nat, Nat.max(lo, Nat.min(x, hi)), lo, w2.max_l(lo, Nat.min(x, hi), le))
    case False{}:
      w2.held_hi(x, lo, hi, Nat.is_lt(hi, x), {==}, lohi, LA.pf.not_lt_le(x, lo, ec))

def w2.clamp_held(+x: Nat, +lo: Nat, +hi: Nat, lohi: {Nat.is_le(lo, hi) == True{} : Bool}) -> {Fx.clamp(x, lo, hi) == Nat.max(lo, Nat.min(x, hi)) : Nat}:
  w2.held_lo(x, lo, hi, Nat.is_lt(x, lo), {==}, lohi)

def Facts.facts_google_budget_held(b, c, l, ordered):
  w2.clamp_held(Maybe.default(&2, Nat, Fx.Customs.at(c, l), Fx.Budgets.at(b, l)), Fx.Budgets.minimal(b), Fx.Budgets.high(b), LA.pf.ord_mh(b, ordered))
