# eukhe: lemmas the proofs of area admission share: bool

import Base
import ../../../bend/admission.bend as Ad
import ./logic.bend as LALogic

def ad.and_ff(x: Bool, y: Bool) -> {Bool.and(x, False{}) == Bool.and(y, False{}) : Bool}:
  match x y:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def ad.and_f(x: Bool) -> {Bool.and(x, False{}) == False{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def ad.and_t(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      LALogic.ad.absurd({Bool.and(False{}, b) == True{} : Bool}, ea)

def ad.or_t(x: Bool) -> {Bool.or(x, True{}) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def ad.not_none(-m: Maybe<&2, Ad.Cls>, e: {m == None{} : Maybe<&2, Ad.Cls>}) -> {Bool.not(Maybe.is_some(&2, Ad.Cls, m)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Ad.Cls>, m, None{}, e) : {Bool.not(Maybe.is_some(&2, Ad.Cls, _)) == True{} : Bool}
  {==}

def ad.grant_none(+l: Ad.Lim, +t: List<&2, Ad.Tk>, ed: {Ad.pick(l, t) == None{} : Maybe<&2, Ad.Cls>}, cm: {Ad.calm(t) == True{} : Bool}) -> {LALogic.ad.ok(l, t) == True{} : Bool}:
  +p = Ad.pick(l, t)
  ad.and_t(Bool.not(Maybe.is_some(&2, Ad.Cls, p)), Ad.calm(t), ad.not_none(p, ed), cm)

# an interactive waiter: no background slot is held
def ad.calm_hb0(+hi: Nat, -w: Nat, hb: Nat, c: {Ad.calm.n(hi, 1n+w, hb) == True{} : Bool}) -> {hb == 0n : Nat}:
  match hb:
    case 0n:
      {==}
    case 1n+x:
      LALogic.ad.absurd({1n+x == 0n : Nat}, Equal.trans(Bool, False{}, Bool.and(Ad.isz(hi), False{}), True{}, Equal.sym(Bool, Bool.and(Ad.isz(hi), False{}), False{}, ad.and_f(Ad.isz(hi))), c))
