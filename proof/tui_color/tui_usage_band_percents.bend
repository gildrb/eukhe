# eukhe: the proof of LAW tui_usage_band_percents
# An unknown window reaches nothing on both sides. In a known window x
# the model counts the shares 1/2, 7/10 and 9/10 that t reaches
# (x num <= t den); the requirement asks from the top whether t reaches
# 90%, 70%, 50% (x p <= 100 t). Each share test is its percent test with
# both sides scaled by 50 or by 10 (bo.scale, bo.half, bo.seven, bo.nine);
# reaching 90% reaches 70% and reaching 70% reaches 50% (bo.down), so the
# count of shares reached is the requirement's level (bo.level).

import Base
import ../../bend/tui_color.bend as TC
import ../../laws/tui_color.bend as TuiColor
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

# b < a gives b (1 + mp) < a (1 + mp)
def bo.mul_lt(+b: Nat, +a: Nat, +mp: Nat, +h: {Nat.is_lt(b, a) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(b, 1n+mp), Nat.mul(a, 1n+mp)) == True{} : Bool}:
  match b a:
    case p 0n:
      LLogicLogic.pu.absurd_ft({Nat.is_lt(Nat.mul(p, 1n+mp), Nat.mul(0n, 1n+mp)) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(p, 0n), True{}, LNat.pu.lt_zero_f(p), h))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      LA.pu.lt_add_l(1n+mp, Nat.mul(p, 1n+mp), Nat.mul(q, 1n+mp), bo.mul_lt(p, q, mp, h))

def bo.scale.pick(c: Bool, +a: Nat, +b: Nat, +mp: Nat, +e: {Nat.is_le(a, b) == c : Bool}) -> {Nat.is_le(Nat.mul(a, 1n+mp), Nat.mul(b, 1n+mp)) == c : Bool}:
  match c:
    case True{}:
      LA.pu.mul_le_mono_l(a, b, 1n+mp, e)
    case False{}:
      LA.pu.lt_not_le(Nat.mul(b, 1n+mp), Nat.mul(a, 1n+mp), bo.mul_lt(b, a, mp, LA.pu.not_le_lt(a, b, e)))

# scaling both sides by 1 + mp keeps a <= test
def bo.scale(+a: Nat, +b: Nat, +mp: Nat) -> {Nat.is_le(Nat.mul(a, 1n+mp), Nat.mul(b, 1n+mp)) == Nat.is_le(a, b) : Bool}:
  bo.scale.pick(Nat.is_le(a, b), a, b, mp, {==})

# 50% is the share 1/2
def bo.half(+x: Nat, +t: Nat) -> {TuiColor.usage_reaches(t, x, 50n) == Nat.is_le(Nat.mul(x, 1n), Nat.mul(t, 2n)) : Bool}:
  %LA.pu.mul_assoc(x, 1n, 50n) : {Nat.is_le(_, Nat.mul(t, 100n)) == Nat.is_le(Nat.mul(x, 1n), Nat.mul(t, 2n)) : Bool}
  %LA.pu.mul_assoc(t, 2n, 50n) : {Nat.is_le(Nat.mul(Nat.mul(x, 1n), 50n), _) == Nat.is_le(Nat.mul(x, 1n), Nat.mul(t, 2n)) : Bool}
  bo.scale(Nat.mul(x, 1n), Nat.mul(t, 2n), 49n)

# 70% is the share 7/10
def bo.seven(+x: Nat, +t: Nat) -> {TuiColor.usage_reaches(t, x, 70n) == Nat.is_le(Nat.mul(x, 7n), Nat.mul(t, 10n)) : Bool}:
  %LA.pu.mul_assoc(x, 7n, 10n) : {Nat.is_le(_, Nat.mul(t, 100n)) == Nat.is_le(Nat.mul(x, 7n), Nat.mul(t, 10n)) : Bool}
  %LA.pu.mul_assoc(t, 10n, 10n) : {Nat.is_le(Nat.mul(Nat.mul(x, 7n), 10n), _) == Nat.is_le(Nat.mul(x, 7n), Nat.mul(t, 10n)) : Bool}
  bo.scale(Nat.mul(x, 7n), Nat.mul(t, 10n), 9n)

# 90% is the share 9/10
def bo.nine(+x: Nat, +t: Nat) -> {TuiColor.usage_reaches(t, x, 90n) == Nat.is_le(Nat.mul(x, 9n), Nat.mul(t, 10n)) : Bool}:
  %LA.pu.mul_assoc(x, 9n, 10n) : {Nat.is_le(_, Nat.mul(t, 100n)) == Nat.is_le(Nat.mul(x, 9n), Nat.mul(t, 10n)) : Bool}
  %LA.pu.mul_assoc(t, 10n, 10n) : {Nat.is_le(Nat.mul(Nat.mul(x, 9n), 10n), _) == Nat.is_le(Nat.mul(x, 9n), Nat.mul(t, 10n)) : Bool}
  bo.scale(Nat.mul(x, 9n), Nat.mul(t, 10n), 9n)

# reaching p percent reaches every q <= p percent
def bo.down(+x: Nat, +t: Nat, +q: Nat, +p: Nat, +qp: {Nat.is_le(q, p) == True{} : Bool}, +h: {TuiColor.usage_reaches(t, x, p) == True{} : Bool}) -> {TuiColor.usage_reaches(t, x, q) == True{} : Bool}:
  LNat.pu.le_trans(Nat.mul(x, q), Nat.mul(x, p), Nat.mul(t, 100n), LA.pu.mul_le_mono_r(x, q, p, qp), h)

# a lower percent missed while a higher one is reached: impossible
def bo.gap(-G: Type, +x: Nat, +t: Nat, +q: Nat, +p: Nat, +qp: {Nat.is_le(q, p) == True{} : Bool}, +h: {TuiColor.usage_reaches(t, x, p) == True{} : Bool}, +no: {TuiColor.usage_reaches(t, x, q) == False{} : Bool}) -> G:
  LLogicLogic.pu.absurd_ft(G, Equal.trans(Bool, False{}, TuiColor.usage_reaches(t, x, q), True{}, Equal.sym(Bool, TuiColor.usage_reaches(t, x, q), False{}, no), bo.down(x, t, q, p, qp, h)))

# the count of the percents reached is the requirement's level
def bo.level(c: Bool, b: Bool, a: Bool, +x: Nat, +t: Nat,
  +ec: {TuiColor.usage_reaches(t, x, 90n) == c : Bool}, +eb: {TuiColor.usage_reaches(t, x, 70n) == b : Bool}, +ea: {TuiColor.usage_reaches(t, x, 50n) == a : Bool})
  -> {Nat.add(TC.one(a), Nat.add(TC.one(b), Nat.add(TC.one(c), 0n))) == TuiColor.usage_level.from(c, b, a) : Nat}:
  match c b a:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      bo.gap({Nat.add(TC.one(False{}), Nat.add(TC.one(True{}), Nat.add(TC.one(True{}), 0n))) == TuiColor.usage_level.from(True{}, True{}, False{}) : Nat}, x, t, 50n, 70n, {==}, eb, ea)
    case True{} False{} True{}:
      bo.gap({Nat.add(TC.one(True{}), Nat.add(TC.one(False{}), Nat.add(TC.one(True{}), 0n))) == TuiColor.usage_level.from(True{}, False{}, True{}) : Nat}, x, t, 70n, 90n, {==}, ec, eb)
    case True{} False{} False{}:
      bo.gap({Nat.add(TC.one(False{}), Nat.add(TC.one(False{}), Nat.add(TC.one(True{}), 0n))) == TuiColor.usage_level.from(True{}, False{}, False{}) : Nat}, x, t, 70n, 90n, {==}, ec, eb)
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      bo.gap({Nat.add(TC.one(False{}), Nat.add(TC.one(True{}), Nat.add(TC.one(False{}), 0n))) == TuiColor.usage_level.from(False{}, True{}, False{}) : Nat}, x, t, 50n, 70n, {==}, eb, ea)
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# the model's count of the shares a, b, c (1/2, 7/10, 9/10) is the
# requirement's level
def bo.fin(+t: Nat, +x: Nat, +A: Bool, +B: Bool, +C: Bool,
  +eA: {TuiColor.usage_reaches(t, x, 50n) == A : Bool}, +eB: {TuiColor.usage_reaches(t, x, 70n) == B : Bool}, +eC: {TuiColor.usage_reaches(t, x, 90n) == C : Bool})
  -> {Nat.add(TC.one(A), Nat.add(TC.one(B), Nat.add(TC.one(C), 0n))) == TuiColor.usage_level.from(TuiColor.usage_reaches(t, x, 90n), TuiColor.usage_reaches(t, x, 70n), TuiColor.usage_reaches(t, x, 50n)) : Nat}:
  +lhs = Nat.add(TC.one(A), Nat.add(TC.one(B), Nat.add(TC.one(C), 0n)))
  %Equal.sym(Bool, TuiColor.usage_reaches(t, x, 90n), C, eC) : {lhs == TuiColor.usage_level.from(_, TuiColor.usage_reaches(t, x, 70n), TuiColor.usage_reaches(t, x, 50n)) : Nat}
  %Equal.sym(Bool, TuiColor.usage_reaches(t, x, 70n), B, eB) : {lhs == TuiColor.usage_level.from(C, _, TuiColor.usage_reaches(t, x, 50n)) : Nat}
  %Equal.sym(Bool, TuiColor.usage_reaches(t, x, 50n), A, eA) : {lhs == TuiColor.usage_level.from(C, B, _) : Nat}
  bo.level(C, B, A, x, t, eC, eB, eA)

def TuiColor.tui_usage_band_percents(t, w):
  match w:
    case 0n:
      {==}
    case 1n+v:
      +x = {1n+v : Nat}
      bo.fin(t, x, Nat.is_le(Nat.mul(x, 1n), Nat.mul(t, 2n)), Nat.is_le(Nat.mul(x, 7n), Nat.mul(t, 10n)), Nat.is_le(Nat.mul(x, 9n), Nat.mul(t, 10n)), bo.half(x, t), bo.seven(x, t), bo.nine(x, t))
