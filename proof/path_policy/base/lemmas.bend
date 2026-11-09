# eukhe: shared lemmas of proof/path_policy: Bool and Nat equality, ids.eq
# soundness, and the real location of a path judged not secret.

import Base
import ../../../bend/path_policy.bend as Pp
import ../../../bend/tools.bend as Tl
import ../../base/logic/logic.bend as LLogicLogic
import ../base.bend as LA

def pp.or_false_l(a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      LLogicLogic.pp.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def pp.or_false_r(a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      LLogicLogic.pp.absurd({b == False{} : Bool}, h)
    case False{}:
      h

def pp.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LA.pp.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      LA.pp.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pp.eq_true(p, q, h))

def pp.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LA.pp.absurdF({False{} == True{} : Bool}, h)

# two lists that ids.eq calls equal are equal
def pp.ids_sound(a: List<&2, Nat>, b: List<&2, Nat>, +h: {Tl.ids.eq(a, b) == True{} : Bool}) -> {a == b : List<&2, Nat>}:
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          {==}
        case y <> yr:
          LA.pp.absurdF({Nil{} == y <> yr : List<&2, Nat>}, h)
    case +x <> +xr:
      match b:
        case Nil{}:
          LA.pp.absurdF({x <> xr == Nil{} : List<&2, Nat>}, h)
        case +y <> +yr:
          %pp.eq_true(x, y, pp.and_l(Nat.is_eq(x, y), Tl.ids.eq(xr, yr), h)) : {x <> xr == _ <> yr : List<&2, Nat>}
          %pp.ids_sound(xr, yr, LA.pp.and_r(Nat.is_eq(x, y), Tl.ids.eq(xr, yr), h)) : {x <> xr == x <> _ : List<&2, Nat>}
          {==}

# 4. The store
# ------------

# demote keeps a class that is not a secret not a secret
def pp.demote_secret(c: Pp.Cls, looped: Bool, h: {Pp.Cls.secret(Pp.demote(c, looped)) == False{} : Bool}) -> {Pp.Cls.secret(c) == False{} : Bool}:
  match c:
    case Pp.Inside{}:
      {==}
    case Pp.Outside{}:
      {==}
    case Pp.Protected{}:
      {==}
    case Pp.Secret{}:
      h

# the real location of a path judged not secret is not a secret
def pp.res_secret(+pol: Pp.Pol, r: Pp.Res, h: {Pp.Cls.secret(Pp.class_res(pol, r)) == False{} : Bool}) -> {Pp.Cls.secret(Pp.class_of(pol, Pp.Res.at(r))) == False{} : Bool}:
  match r:
    case Pp.Res{+at, +looped}:
      pp.demote_secret(Pp.class_of(pol, at), looped, h)
