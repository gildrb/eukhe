# eukhe: lemmas of the proof of LAW facts_ffi_exact: the model's fit and
# Google budget in the closed forms of the laws' spec terms

import Base
import ../../../bend/facts.bend as Fx
import ../../../laws/facts/model.bend as Facts
import ../../base/logic/logic.bend as LLogicLogic
import ../../base/nat.bend as LNat
import ../base.bend as LA

# the fit without a caller's cap: the model's cap through the window
def fem.fit_model(+mm: Nat, +b: Nat, +a: Nat, +win: Fx.Win) -> {Fx.fit(None{}, mm, b, a, win) == Facts.budgets.fit(Fx.cap.shrink(mm, win), b, a) : Fx.Fit}:
  {==}

# the fit with the caller's cap x: x plus the budget, at most mm, through
# the window
def fem.fit_caller(+x: Nat, +mm: Nat, +b: Nat, +a: Nat, +win: Fx.Win) -> {Fx.fit(Some{x}, mm, b, a, win) == Facts.budgets.fit(Fx.cap.shrink(Nat.min(Nat.add(x, b), mm), win), b, a) : Fx.Fit}:
  %LA.w2.cap_sum(x, mm, b) : {Fx.fit(Some{x}, mm, b, a, win) == Facts.budgets.fit(Fx.cap.shrink(_, win), b, a) : Fx.Fit}
  {==}

def fem.cong1(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  %e : {1n+a == 1n+_ : Nat}
  {==}

def fem.max_l(+a: Nat, +y: Nat, h: {Nat.is_le(y, a) == True{} : Bool}) -> {Nat.max(a, y) == a : Nat}:
  match a y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LLogicLogic.pq.absurdF({1n+q == 0n : Nat}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      fem.cong1(Nat.max(p, q), p, fem.max_l(p, q, h))

def fem.max_r(+a: Nat, +y: Nat, h: {Nat.is_le(a, y) == True{} : Bool}) -> {Nat.max(a, y) == y : Nat}:
  match a y:
    case 0n y:
      {==}
    case 1n+p 0n:
      LLogicLogic.pq.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      fem.cong1(Nat.max(p, q), q, fem.max_r(p, q, h))

def fem.min_l(+x: Nat, +y: Nat, h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.min(x, y) == x : Nat}:
  match x y:
    case 0n y:
      {==}
    case 1n+p 0n:
      LLogicLogic.pq.absurdF({0n == 1n+p : Nat}, h)
    case 1n+p 1n+q:
      fem.cong1(Nat.min(p, q), p, fem.min_l(p, q, h))

def fem.min_le_l(+x: Nat, +y: Nat) -> {Nat.is_le(Nat.min(x, y), x) == True{} : Bool}:
  match x y:
    case 0n y:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      fem.min_le_l(p, q)

def fem.lt_le(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n b:
      LNat.pq.le0(b)
    case 1n+p 0n:
      LLogicLogic.pq.absurdF({False{} == True{} : Bool}, h)
    case 1n+p 1n+q:
      fem.lt_le(p, q, h)

# x held inside lo..hi by the clamp is max(lo, min(x, hi))
def fem.held_hi(+x: Nat, +lo: Nat, +hi: Nat, g: Bool, eg: {Nat.is_lt(hi, x) == g : Bool}, lohi: {Nat.is_le(lo, hi) == True{} : Bool}, lox: {Nat.is_le(lo, x) == True{} : Bool}) -> {Fx.clamp.hi(g, x, hi) == Nat.max(lo, Nat.min(x, hi)) : Nat}:
  match g:
    case True{}:
      %Equal.sym(Nat, Nat.min(x, hi), hi, LA.w2.min_r(x, hi, fem.lt_le(hi, x, eg))) : {hi == Nat.max(lo, _) : Nat}
      Equal.sym(Nat, Nat.max(lo, hi), hi, fem.max_r(lo, hi, lohi))
    case False{}:
      %Equal.sym(Nat, Nat.min(x, hi), x, fem.min_l(x, hi, LA.pf.not_lt_le(hi, x, eg))) : {x == Nat.max(lo, _) : Nat}
      Equal.sym(Nat, Nat.max(lo, x), x, fem.max_r(lo, x, lox))

def fem.held_lo(+x: Nat, +lo: Nat, +hi: Nat, c: Bool, ec: {Nat.is_lt(x, lo) == c : Bool}, lohi: {Nat.is_le(lo, hi) == True{} : Bool}) -> {Fx.clamp.lo(c, x, lo, hi) == Nat.max(lo, Nat.min(x, hi)) : Nat}:
  match c:
    case True{}:
      +le = LA.pf.le_trans(Nat.min(x, hi), x, lo, fem.min_le_l(x, hi), fem.lt_le(x, lo, ec))
      Equal.sym(Nat, Nat.max(lo, Nat.min(x, hi)), lo, fem.max_l(lo, Nat.min(x, hi), le))
    case False{}:
      fem.held_hi(x, lo, hi, Nat.is_lt(hi, x), {==}, lohi, LA.pf.not_lt_le(x, lo, ec))

def fem.clamp_held(+x: Nat, +lo: Nat, +hi: Nat, lohi: {Nat.is_le(lo, hi) == True{} : Bool}) -> {Fx.clamp(x, lo, hi) == Nat.max(lo, Nat.min(x, hi)) : Nat}:
  fem.held_lo(x, lo, hi, Nat.is_lt(x, lo), {==}, lohi)

# the Google budget of an ordered rule: the user's budget of the level,
# else the rule's, held inside minimal..high
def fem.held(+b: Fx.Budgets, c: Fx.Customs, +l: Fx.Lv, +ordered: {Fx.Budgets.ordered(b) == True{} : Bool}) -> {Fx.gtokens(b, c, l) == Facts.budgets.held(Maybe.default(&2, Nat, Fx.Customs.at(c, l), Fx.Budgets.at(b, l)), Fx.Budgets.minimal(b), Fx.Budgets.high(b)) : Nat}:
  fem.clamp_held(Maybe.default(&2, Nat, Fx.Customs.at(c, l), Fx.Budgets.at(b, l)), Fx.Budgets.minimal(b), Fx.Budgets.high(b), LA.pf.ord_mh(b, ordered))
