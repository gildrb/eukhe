# eukhe: lemmas the proofs of area tree share: nat

import Base
import ../../../bend/tree.bend as Tr
import ../../base/bool/and.bend as LBoolAnd
import ../../base/bool/misc.bend as LBoolMisc
import ../../base/nat/is_eq.bend as LNatIsEq
import ../../base/nat/is_lt.bend as LNatIsLt
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

def pt.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LBoolMisc.tree.pt.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      LBoolMisc.tree.pt.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pt.eq_true(p, q, h))

def pt.lt_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_lt(a, b) == True{} : Bool}, bc: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case _ 0n _:
      LBoolMisc.tree.pt.absurdF({Nat.is_lt(a, c) == True{} : Bool}, ab)
    case _ 1n+q 0n:
      LBoolMisc.tree.pt.absurdF({Nat.is_lt(a, 0n) == True{} : Bool}, bc)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 1n+r:
      pt.lt_trans(p, q, r, ab, bc)

def pt.cmp_eq(a: Nat, b: Nat, h: {Nat.cmp(a, b) == EQ{} : Cmp}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      %h : LALogic.pt.CD(_, Unit, {0n == 1n+q : Nat}, Unit)
      Unit{}
    case 1n+p 0n:
      %h : LALogic.pt.CD(_, Unit, {1n+p == 0n : Nat}, Unit)
      Unit{}
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pt.cmp_eq(p, q, h))

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

# Keys that differ
# ----------------

def pt.ne_go(+a: Nat, +x: Nat, c: Bool, ec: {Nat.is_eq(a, x) == c : Bool}, -f: Nat -> Bool, na: {f(a) == False{} : Bool}, hx: {f(x) == True{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      +fe = Equal.cong(Nat, Bool, f, a, x, pt.eq_true(a, x, ec))
      LALogic.pt.void({True{} == False{} : Bool}, LABool.pt.flip(f(x), hx, Equal.trans(Bool, f(x), f(a), False{}, Equal.sym(Bool, f(a), f(x), fe), na)))
    case False{}:
      {==}

# a key a test rejects is not a key it accepts
def pt.ne_by(+a: Nat, +x: Nat, -f: Nat -> Bool, na: {f(a) == False{} : Bool}, hx: {f(x) == True{} : Bool}) -> {Nat.is_eq(a, x) == False{} : Bool}:
  pt.ne_go(a, x, Nat.is_eq(a, x), {==}, f, na, hx)

def pt.ne_by2(+a: Nat, +x: Nat, -f: Nat -> Bool, ha: {f(a) == True{} : Bool}, nx: {f(x) == False{} : Bool}) -> {Nat.is_eq(a, x) == False{} : Bool}:
  LNatIsEq.pt.ne_comm(x, a, pt.ne_by(x, a, f, nx, ha))

def pt.eq_of(+a: Nat, +b: Nat, ab: {a == b : Nat}) -> {Nat.is_eq(b, a) == True{} : Bool}:
  %ab : {Nat.is_eq(_, a) == True{} : Bool}
  Equal.sym(Bool, True{}, Nat.is_eq(a, a), pt.eq_refl(a))

def tc.nall_cons(+k: Nat, +gone: List<&2, Nat>, +x: Nat, +kx: {Nat.is_lt(k, x) == False{} : Bool}, +ng: {LABool.tc.nall(gone, x) == True{} : Bool}) -> {LABool.tc.nall(k <> gone, x) == True{} : Bool}:
  LBoolAnd.tree.pt.and_t(Bool.not(Nat.is_lt(k, x)), LABool.tc.nall(gone, x), LBoolMisc.pt.not_t(Nat.is_lt(k, x), kx), ng)

# The largest parent key of a fork

def tc.ge_trans(a: Nat, b: Nat, c: Nat, +ab: {Nat.is_ge(a, b) == True{} : Bool}, +bc: {Nat.is_ge(b, c) == True{} : Bool}) -> {Nat.is_ge(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+r:
      LBoolMisc.pt.absurd({Nat.is_ge(0n, 1n+r) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, bc))
    case 0n 1n+q _:
      LBoolMisc.pt.absurd({Nat.is_ge(0n, c) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, ab))
    case 1n+p _ 0n:
      {==}
    case 1n+p 0n 1n+r:
      LBoolMisc.pt.absurd({Nat.is_ge(1n+p, 1n+r) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, bc))
    case 1n+p 1n+q 1n+r:
      tc.ge_trans(p, q, r, ab, bc)

# b at or above p and below x: p is below x
def tc.ge_lt(b: Nat, p: Nat, x: Nat, +bp: {Nat.is_ge(b, p) == True{} : Bool}, +bx: {Nat.is_lt(b, x) == True{} : Bool}) -> {Nat.is_lt(p, x) == True{} : Bool}:
  match b p x:
    case _ _ 0n:
      LBoolMisc.tree.pt.absurdF({Nat.is_lt(p, 0n) == True{} : Bool}, bx)
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 1n+r:
      LBoolMisc.pt.absurd({Nat.is_lt(1n+q, 1n+r) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, bp))
    case 1n+a 0n 1n+r:
      {==}
    case 1n+a 1n+q 1n+r:
      tc.ge_lt(a, q, r, bp, bx)

def tc.mpok_gl(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {LABool.tc.mpok(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {Nat.is_ge(mp, Tr.KMap.mp(l)) == True{} : Bool}:
  +h2 = LBoolAnd.tree.pt.and_r(LABool.tc.mpok(r), Bool.and(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r))), LABool.tc.mpok_rest(mid, mp, l, r, h))
  LBoolAnd.tree.pt.and_l(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r)), h2)

def tc.mpok_gr(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {LABool.tc.mpok(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {Nat.is_ge(mp, Tr.KMap.mp(r)) == True{} : Bool}:
  +h2 = LBoolAnd.tree.pt.and_r(LABool.tc.mpok(r), Bool.and(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r))), LABool.tc.mpok_rest(mid, mp, l, r, h))
  LBoolAnd.tree.pt.and_r(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r)), h2)

def tc.ple_mono(A: List<&2, Tr.Ent>, +b: Nat, +c: Nat, +pa: {LABool.tc.ple(A, b) == True{} : Bool}, +cb: {Nat.is_ge(c, b) == True{} : Bool}) -> {LABool.tc.ple(A, c) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case +e <> +r:
      LBoolAnd.tree.pt.and_t(Nat.is_ge(c, Tr.Ent.p(e)), LABool.tc.ple(r, c), tc.ge_trans(c, b, Tr.Ent.p(e), cb, LBoolAnd.tree.pt.and_l(Nat.is_ge(b, Tr.Ent.p(e)), LABool.tc.ple(r, b), pa)), tc.ple_mono(r, b, c, LBoolAnd.tree.pt.and_r(Nat.is_ge(b, Tr.Ent.p(e)), LABool.tc.ple(r, b), pa), cb))

def tc.nokey_ge(t: List<&2, Tr.Ent>, +b: Nat, +x: Nat, +gb: {LBoolMisc.tc.ge(t, b) == True{} : Bool}, +xb: {Nat.is_lt(x, b) == True{} : Bool}) -> {LABool.tc.nokey(t, x) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +e <> +r:
      LBoolAnd.tree.pt.and_t(Bool.not(Nat.is_eq(Tr.Ent.k(e), x)), LABool.tc.nokey(r, x), LBoolMisc.pt.not_t(Nat.is_eq(Tr.Ent.k(e), x), LNatIsLt.tc.ge_miss(e, b, x, LNatIsLt.tc.ge_head(e, r, b, gb), xb)), tc.nokey_ge(r, b, x, LBoolAnd.tc.ge_tail(e, r, b, gb), xb))

def tc.nokey_lt(t: List<&2, Tr.Ent>, +b: Nat, +x: Nat, +lb: {LBoolMisc.tc.lt(t, b) == True{} : Bool}, +xb: {Nat.is_lt(x, b) == False{} : Bool}) -> {LABool.tc.nokey(t, x) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +e <> +r:
      LBoolAnd.tree.pt.and_t(Bool.not(Nat.is_eq(Tr.Ent.k(e), x)), LABool.tc.nokey(r, x), LBoolMisc.pt.not_t(Nat.is_eq(Tr.Ent.k(e), x), LNatIsLt.tc.lt_miss(e, b, x, LNatIsLt.tc.lt_head(e, r, b, lb), xb)), tc.nokey_lt(r, b, x, LBoolAnd.tc.lt_tail(e, r, b, lb), xb))

def tc.gb_hd(c: Bool, +z: Nat, +x: Nat, +k: Nat, +ec: {Nat.is_eq(z, x) == c : Bool}, +h: {Bool.or(c, Nat.is_lt(z, k)) == True{} : Bool}, +kx: {Nat.is_eq(k, x) == False{} : Bool}) -> {Nat.is_eq(z, k) == False{} : Bool}:
  match c:
    case True{}:
      +zx = pt.eq_true(z, x, ec)
      %Equal.sym(Nat, z, x, zx) : {Nat.is_eq(_, k) == False{} : Bool}
      LNatIsEq.pt.ne_comm(k, x, kx)
    case False{}:
      LNatIsEq.pt.lt_ne(z, k, h)

def tc.nlt_go(+a: Nat, +b: Nat, +c: Nat, d: Bool, +ed: {Nat.is_lt(c, b) == d : Bool}, +ac: {Nat.is_lt(a, c) == True{} : Bool}, +nab: {Nat.is_lt(a, b) == False{} : Bool}) -> {d == False{} : Bool}:
  match d:
    case True{}:
      LBoolMisc.pt.absurd({True{} == False{} : Bool}, Equal.trans(Bool, True{}, Nat.is_lt(a, b), False{}, Equal.sym(Bool, Nat.is_lt(a, b), True{}, pt.lt_trans(a, c, b, ac, ed)), nab))
    case False{}:
      {==}

# a below c and a not below b: c not below b
def tc.nlt_up(+a: Nat, +b: Nat, +c: Nat, +ac: {Nat.is_lt(a, c) == True{} : Bool}, +nab: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_lt(c, b) == False{} : Bool}:
  tc.nlt_go(a, b, c, Nat.is_lt(c, b), {==}, ac, nab)

# a kept node's key is x or more
def tc.kept_ge(+e: Tr.Ent, +x: Nat, c: Bool, +ec: {Nat.is_eq(Tr.Ent.k(e), x) == c : Bool}, +h: {Bool.or(c, Bool.not(Nat.is_lt(Tr.Ent.p(e), x))) == True{} : Bool}, +pk: {Nat.is_lt(Tr.Ent.p(e), Tr.Ent.k(e)) == True{} : Bool}) -> {Nat.is_lt(Tr.Ent.k(e), x) == False{} : Bool}:
  match c:
    case True{}:
      +kx = pt.eq_true(Tr.Ent.k(e), x, ec)
      %kx : {Nat.is_lt(Tr.Ent.k(e), _) == False{} : Bool}
      LNatIsLt.pt.lt_irrefl(Tr.Ent.k(e))
    case False{}:
      +px = LBoolMisc.pt.not_f(Nat.is_lt(Tr.Ent.p(e), x), h)
      tc.nlt_up(Tr.Ent.p(e), x, Tr.Ent.k(e), pk, px)

def pd.lt_add2(n: Nat) -> {Nat.is_lt(n, 2n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pd.lt_add2(p)
