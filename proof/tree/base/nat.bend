# eukhe: lemmas the proofs of area tree share: nat

import Base
import ../../../bend/tree.bend as Tr
import ../../base/bool.bend as LBool
import ../../base/logic/bool.bend as LLogicBool
import ../../base/logic/logic.bend as LLogicLogic
import ../../base/nat.bend as LNat
import ./bool.bend as LABool
import ./logic.bend as LALogic

# Numbers
# -------

def pt.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pt.eq_refl(p)

def pt.lt_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_lt(a, b) == True{} : Bool}, bc: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case _ 0n _:
      LLogicLogic.tree.pt.absurdF({Nat.is_lt(a, c) == True{} : Bool}, ab)
    case _ 1n+q 0n:
      LLogicLogic.tree.pt.absurdF({Nat.is_lt(a, 0n) == True{} : Bool}, bc)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 1n+r:
      pt.lt_trans(p, q, r, ab, bc)

def pt.cmp_gt(a: Nat, b: Nat, h: {Nat.cmp(a, b) == GT{} : Cmp}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      %h : LALogic.pt.CD(_, Unit, Unit, {Nat.is_lt(0n, 0n) == True{} : Bool})
      Unit{}
    case 0n 1n+q:
      %h : LALogic.pt.CD(_, Unit, Unit, {Nat.is_lt(1n+q, 0n) == True{} : Bool})
      Unit{}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pt.cmp_gt(p, q, h)

def pt.cmp_lt(+a: Nat, +b: Nat, h: {Nat.cmp(a, b) == LT{} : Cmp}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  %Equal.sym(Cmp, Nat.cmp(a, b), LT{}, h) : {Cmp.is_lt(_) == True{} : Bool}
  {==}

def pt.ne_at(+a: Nat, +y: Nat, +x: Nat, ay: {a == y : Nat}, ne: {Nat.is_eq(y, x) == False{} : Bool}) -> {Nat.is_eq(a, x) == False{} : Bool}:
  %Equal.sym(Nat, a, y, ay) : {Nat.is_eq(_, x) == False{} : Bool}
  ne

# a key a test rejects is not a key it accepts
def pt.ne_by(+a: Nat, +x: Nat, -f: Nat -> Bool, na: {f(a) == False{} : Bool}, hx: {f(x) == True{} : Bool}) -> {Nat.is_eq(a, x) == False{} : Bool}:
  LALogic.pt.ne_go(a, x, Nat.is_eq(a, x), {==}, f, na, hx)

def pt.ne_by2(+a: Nat, +x: Nat, -f: Nat -> Bool, ha: {f(a) == True{} : Bool}, nx: {f(x) == False{} : Bool}) -> {Nat.is_eq(a, x) == False{} : Bool}:
  LNat.pt.ne_comm(x, a, pt.ne_by(x, a, f, nx, ha))

def pt.eq_of(+a: Nat, +b: Nat, ab: {a == b : Nat}) -> {Nat.is_eq(b, a) == True{} : Bool}:
  %ab : {Nat.is_eq(_, a) == True{} : Bool}
  Equal.sym(Bool, True{}, Nat.is_eq(a, a), pt.eq_refl(a))

# The largest parent key of a fork

def tc.ge_trans(a: Nat, b: Nat, c: Nat, +ab: {Nat.is_ge(a, b) == True{} : Bool}, +bc: {Nat.is_ge(b, c) == True{} : Bool}) -> {Nat.is_ge(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+r:
      LLogicLogic.pt.absurd({Nat.is_ge(0n, 1n+r) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, bc))
    case 0n 1n+q _:
      LLogicLogic.pt.absurd({Nat.is_ge(0n, c) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, ab))
    case 1n+p _ 0n:
      {==}
    case 1n+p 0n 1n+r:
      LLogicLogic.pt.absurd({Nat.is_ge(1n+p, 1n+r) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, bc))
    case 1n+p 1n+q 1n+r:
      tc.ge_trans(p, q, r, ab, bc)

# b at or above p and below x: p is below x
def tc.ge_lt(b: Nat, p: Nat, x: Nat, +bp: {Nat.is_ge(b, p) == True{} : Bool}, +bx: {Nat.is_lt(b, x) == True{} : Bool}) -> {Nat.is_lt(p, x) == True{} : Bool}:
  match b p x:
    case _ _ 0n:
      LLogicLogic.tree.pt.absurdF({Nat.is_lt(p, 0n) == True{} : Bool}, bx)
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 1n+r:
      LLogicLogic.pt.absurd({Nat.is_lt(1n+q, 1n+r) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, bp))
    case 1n+a 0n 1n+r:
      {==}
    case 1n+a 1n+q 1n+r:
      tc.ge_lt(a, q, r, bp, bx)

def tc.mpok_gl(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {LALogic.tc.mpok(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {Nat.is_ge(mp, Tr.KMap.mp(l)) == True{} : Bool}:
  +h2 = LLogicBool.tree.pt.and_r(LALogic.tc.mpok(r), Bool.and(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r))), LABool.tc.mpok_rest(mid, mp, l, r, h))
  LLogicBool.tree.pt.and_l(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r)), h2)

def tc.mpok_gr(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {LALogic.tc.mpok(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {Nat.is_ge(mp, Tr.KMap.mp(r)) == True{} : Bool}:
  +h2 = LLogicBool.tree.pt.and_r(LALogic.tc.mpok(r), Bool.and(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r))), LABool.tc.mpok_rest(mid, mp, l, r, h))
  LLogicBool.tree.pt.and_r(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r)), h2)

def tc.ple_mono(A: List<&2, Tr.Ent>, +b: Nat, +c: Nat, +pa: {LALogic.tc.ple(A, b) == True{} : Bool}, +cb: {Nat.is_ge(c, b) == True{} : Bool}) -> {LALogic.tc.ple(A, c) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case +e <> +r:
      LBool.tree.pt.and_t(Nat.is_ge(c, Tr.Ent.p(e)), LALogic.tc.ple(r, c), tc.ge_trans(c, b, Tr.Ent.p(e), cb, LLogicBool.tree.pt.and_l(Nat.is_ge(b, Tr.Ent.p(e)), LALogic.tc.ple(r, b), pa)), tc.ple_mono(r, b, c, LLogicBool.tree.pt.and_r(Nat.is_ge(b, Tr.Ent.p(e)), LALogic.tc.ple(r, b), pa), cb))

def tc.gb_hd(c: Bool, +z: Nat, +x: Nat, +k: Nat, +ec: {Nat.is_eq(z, x) == c : Bool}, +h: {Bool.or(c, Nat.is_lt(z, k)) == True{} : Bool}, +kx: {Nat.is_eq(k, x) == False{} : Bool}) -> {Nat.is_eq(z, k) == False{} : Bool}:
  match c:
    case True{}:
      +zx = LALogic.pt.eq_true(z, x, ec)
      %Equal.sym(Nat, z, x, zx) : {Nat.is_eq(_, k) == False{} : Bool}
      LNat.pt.ne_comm(k, x, kx)
    case False{}:
      LNat.pt.lt_ne(z, k, h)

def tc.nlt_go(+a: Nat, +b: Nat, +c: Nat, d: Bool, +ed: {Nat.is_lt(c, b) == d : Bool}, +ac: {Nat.is_lt(a, c) == True{} : Bool}, +nab: {Nat.is_lt(a, b) == False{} : Bool}) -> {d == False{} : Bool}:
  match d:
    case True{}:
      LLogicLogic.pt.absurd({True{} == False{} : Bool}, Equal.trans(Bool, True{}, Nat.is_lt(a, b), False{}, Equal.sym(Bool, Nat.is_lt(a, b), True{}, pt.lt_trans(a, c, b, ac, ed)), nab))
    case False{}:
      {==}

# a below c and a not below b: c not below b
def tc.nlt_up(+a: Nat, +b: Nat, +c: Nat, +ac: {Nat.is_lt(a, c) == True{} : Bool}, +nab: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_lt(c, b) == False{} : Bool}:
  tc.nlt_go(a, b, c, Nat.is_lt(c, b), {==}, ac, nab)

# a kept node's key is x or more
def tc.kept_ge(+e: Tr.Ent, +x: Nat, c: Bool, +ec: {Nat.is_eq(Tr.Ent.k(e), x) == c : Bool}, +h: {Bool.or(c, Bool.not(Nat.is_lt(Tr.Ent.p(e), x))) == True{} : Bool}, +pk: {Nat.is_lt(Tr.Ent.p(e), Tr.Ent.k(e)) == True{} : Bool}) -> {Nat.is_lt(Tr.Ent.k(e), x) == False{} : Bool}:
  match c:
    case True{}:
      +kx = LALogic.pt.eq_true(Tr.Ent.k(e), x, ec)
      %kx : {Nat.is_lt(Tr.Ent.k(e), _) == False{} : Bool}
      LNat.pt.lt_irrefl(Tr.Ent.k(e))
    case False{}:
      +px = LLogicBool.pt.not_f(Nat.is_lt(Tr.Ent.p(e), x), h)
      tc.nlt_up(Tr.Ent.p(e), x, Tr.Ent.k(e), pk, px)

def pd.lt_add2(n: Nat) -> {Nat.is_lt(n, 2n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pd.lt_add2(p)

# a list with no key x and every parent at most b below x has no node a
# delete of x may remove
def tc.fx_nil(t: List<&2, Tr.Ent>, +x: Nat, +b: Nat, +nk: {LALogic.tc.nokey(t, x) == True{} : Bool}, +pb: {LALogic.tc.ple(t, b) == True{} : Bool}, +bx: {Nat.is_lt(b, x) == True{} : Bool}) -> {LALogic.tc.fx(t, x) == Nil{} : List<&2, Tr.Ent>}:
  match t:
    case Nil{}:
      {==}
    case +e <> +r:
      +ne = LLogicBool.pt.not_f(Nat.is_eq(Tr.Ent.k(e), x), LLogicBool.tree.pt.and_l(Bool.not(Nat.is_eq(Tr.Ent.k(e), x)), LALogic.tc.nokey(r, x), nk))
      +px = tc.ge_lt(b, Tr.Ent.p(e), x, LLogicBool.tree.pt.and_l(Nat.is_ge(b, Tr.Ent.p(e)), LALogic.tc.ple(r, b), pb), bx)
      Equal.trans(List<&2, Tr.Ent>, LALogic.tc.fx(e <> r, x), LALogic.tc.fx(r, x), Nil{}, LALogic.tc.fx_drop(e, r, x, ne, px), tc.fx_nil(r, x, b, LLogicBool.tree.pt.and_r(Bool.not(Nat.is_eq(Tr.Ent.k(e), x)), LALogic.tc.nokey(r, x), nk), LLogicBool.tree.pt.and_r(Nat.is_ge(b, Tr.Ent.p(e)), LALogic.tc.ple(r, b), pb), bx))
