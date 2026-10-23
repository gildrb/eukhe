# eukhe: lemmas the proofs of area tree share: tree/Ent

import Base
import ../../../../bend/tree.bend as Tr
import ../../../base/bool/and.bend as LBoolAnd
import ../../../base/bool/misc.bend as LBoolMisc
import ../../../base/nat/is_eq.bend as LNatIsEq
import ../bool.bend as LABool
import ../list.bend as LAList
import ../maybe.bend as LAMaybe
import ../nat.bend as LANat
import ./misc.bend as LATreeMisc

def tree.pt.none_some(-A: Type, -x: Tr.Ent, e: {None{} == Some{x} : Maybe<&2, Tr.Ent>}) -> A:
  %e : LAMaybe.pt.MD(_, Unit, A)
  Unit{}

def pt.some_none(-A: Type, -x: Tr.Ent, e: {Some{x} == None{} : Maybe<&2, Tr.Ent>}) -> A:
  %e : LAMaybe.pt.MD(_, A, Unit)
  Unit{}

# Nodes
# -----

def pt.ent_eta(e: Tr.Ent) -> {Tr.Ent{Tr.Ent.k(e), Tr.Ent.p(e), Tr.Ent.v(e)} == e : Tr.Ent}:
  match e:
    case Tr.Ent{k, p, v}:
      {==}

def pt.ent_refl(e: Tr.Ent) -> {Tr.Ent.eq(e, e) == True{} : Bool}:
  match e:
    case Tr.Ent{+k, +p, +v}:
      %LANat.pt.eq_refl(k) : {Bool.and(_, Bool.and(Nat.is_eq(p, p), Nat.is_eq(v, v))) == True{} : Bool}
      %LANat.pt.eq_refl(p) : {Bool.and(True{}, Bool.and(_, Nat.is_eq(v, v))) == True{} : Bool}
      %LANat.pt.eq_refl(v) : {Bool.and(True{}, Bool.and(True{}, _)) == True{} : Bool}
      {==}

def pt.ent_true(a: Tr.Ent, b: Tr.Ent, +h: {Tr.Ent.eq(a, b) == True{} : Bool}) -> {a == b : Tr.Ent}:
  match a b:
    case Tr.Ent{+ak, +ap, +av} Tr.Ent{+bk, +bp, +bv}:
      +hk = LANat.pt.eq_true(ak, bk, LBoolAnd.tree.pt.and_l(Nat.is_eq(ak, bk), Bool.and(Nat.is_eq(ap, bp), Nat.is_eq(av, bv)), h))
      +h2 = LBoolAnd.tree.pt.and_r(Nat.is_eq(ak, bk), Bool.and(Nat.is_eq(ap, bp), Nat.is_eq(av, bv)), h)
      +hp = LANat.pt.eq_true(ap, bp, LBoolAnd.tree.pt.and_l(Nat.is_eq(ap, bp), Nat.is_eq(av, bv), h2))
      +hv = LANat.pt.eq_true(av, bv, LBoolAnd.tree.pt.and_r(Nat.is_eq(ap, bp), Nat.is_eq(av, bv), h2))
      %hk : {Tr.Ent{ak, ap, av} == Tr.Ent{_, bp, bv} : Tr.Ent}
      %hp : {Tr.Ent{ak, ap, av} == Tr.Ent{ak, _, bv} : Tr.Ent}
      %hv : {Tr.Ent{ak, ap, av} == Tr.Ent{ak, ap, _} : Tr.Ent}
      {==}

# a lookup that is the same as Some{e} is Some{e}
def pt.same_some(m: Maybe<&2, Tr.Ent>, +e: Tr.Ent, h: {Tr.same(m, Some{e}) == True{} : Bool}) -> {m == Some{e} : Maybe<&2, Tr.Ent>}:
  match m:
    case None{}:
      LBoolMisc.tree.pt.absurdF({None{} == Some{e} : Maybe<&2, Tr.Ent>}, h)
    case Some{x}:
      Equal.cong(Tr.Ent, Maybe<&2, Tr.Ent>, y => Some{y}, x, e, pt.ent_true(x, e, h))

def pt.same_refl(+e: Tr.Ent) -> {Tr.same(Some{e}, Some{e}) == True{} : Bool}:
  pt.ent_refl(e)

def pt.val(m: Maybe<&2, Tr.Ent>, d: Tr.Ent) -> Tr.Ent:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def tree.pt.some_inj(+x: Tr.Ent, +y: Tr.Ent, h: {Some{x} == Some{y} : Maybe<&2, Tr.Ent>}) -> {x == y : Tr.Ent}:
  Equal.cong(Maybe<&2, Tr.Ent>, Tr.Ent, m => pt.val(m, x), Some{x}, Some{y}, h)

def tc.fd_at(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool, +eh: {Tr.gone.at(e <> r, gone) == hit : Bool}, +x: Nat, c: Bool, +ec: {Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x))) == c : Bool}, +ng: {LABool.tc.nall(gone, x) == True{} : Bool}, +g: {LABool.tc.gb(gone, x, e <> r) == True{} : Bool}, +pk: {Nat.is_lt(Tr.Ent.p(e), Tr.Ent.k(e)) == True{} : Bool}, +ih1: {LAList.tc.dgo(r, gone, Tr.gone.at(r, gone)) == LAList.tc.dgo(LAList.tc.fx(r, x), gone, Tr.gone.at(LAList.tc.fx(r, x), gone)) : List<&2, Nat>}, ih2: {Nat.is_lt(Tr.Ent.k(e), x) == False{} : Bool} -> {LAList.tc.dgo(r, Tr.Ent.k(e) <> gone, Tr.gone.at(r, Tr.Ent.k(e) <> gone)) == LAList.tc.dgo(LAList.tc.fx(r, x), Tr.Ent.k(e) <> gone, Tr.gone.at(LAList.tc.fx(r, x), Tr.Ent.k(e) <> gone)) : List<&2, Nat>}) -> {LAList.tc.dgo(e <> r, gone, hit) == LAList.tc.dgo(LAList.tc.fx.at(c, e, LAList.tc.fx(r, x)), gone, Tr.gone.at(LAList.tc.fx.at(c, e, LAList.tc.fx(r, x)), gone)) : List<&2, Nat>}:
  match c:
    case True{}:
      +G = Bool.or(Tr.elem(gone, Tr.Ent.k(e)), Tr.elem(gone, Tr.Ent.p(e)))
      +kx = LANat.tc.kept_ge(e, x, Nat.is_eq(Tr.Ent.k(e), x), {==}, ec, pk)
      %Equal.sym(Bool, G, hit, eh) : {LAList.tc.dgo(e <> r, gone, hit) == LAList.tc.dgo(e <> LAList.tc.fx(r, x), gone, _) : List<&2, Nat>}
      LATreeMisc.tc.dg_ge(hit, e, r, LAList.tc.fx(r, x), gone, ih1, ih2(kx))
    case False{}:
      +ne = LABool.pt.or_l(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x)), ec)
      +px = LABool.tc.not_ff(Nat.is_lt(Tr.Ent.p(e), x), LABool.pt.or_r(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x)), ec))
      +nk = LATreeMisc.tc.gb_elem(gone, x, e, r, g, ne)
      +np = LATreeMisc.tc.elem_none(gone, x, Tr.Ent.p(e), ng, px)
      +o = LABool.tc.or_ff(Tr.elem(gone, Tr.Ent.k(e)), Tr.elem(gone, Tr.Ent.p(e)), nk, np)
      +hf = Equal.trans(Bool, hit, Bool.or(Tr.elem(gone, Tr.Ent.k(e)), Tr.elem(gone, Tr.Ent.p(e))), False{}, Equal.sym(Bool, Bool.or(Tr.elem(gone, Tr.Ent.k(e)), Tr.elem(gone, Tr.Ent.p(e))), hit, eh), o)
      %Equal.sym(Bool, hit, False{}, hf) : {LAList.tc.dgo(e <> r, gone, _) == LAList.tc.dgo(LAList.tc.fx(r, x), gone, Tr.gone.at(LAList.tc.fx(r, x), gone)) : List<&2, Nat>}
      ih1

# an unset of a key above the head keeps the head
def tc.unsets_cons(ks: List<&2, Nat>, +e: Tr.Ent, +r: List<&2, Tr.Ent>, +gt: {LABool.tc.gtall(ks, Tr.Ent.k(e)) == True{} : Bool}) -> {LAList.tc.unsets(ks, e <> r) == e <> LAList.tc.unsets(ks, r) : List<&2, Tr.Ent>}:
  match ks:
    case Nil{}:
      {==}
    case +z <> +rest:
      +lt = LBoolAnd.tree.pt.and_l(Nat.is_lt(Tr.Ent.k(e), z), LABool.tc.gtall(rest, Tr.Ent.k(e)), gt)
      +ne = LNatIsEq.pt.lt_ne(Tr.Ent.k(e), z, lt)
      %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(e), z), False{}, ne) : {LAList.tc.unsets(rest, Tr.unset.go(e <> r, z, _)) == e <> LAList.tc.unsets(rest, Tr.unset(r, z)) : List<&2, Tr.Ent>}
      tc.unsets_cons(rest, e, Tr.unset(r, z), LBoolAnd.tree.pt.and_r(Nat.is_lt(Tr.Ent.k(e), z), LABool.tc.gtall(rest, Tr.Ent.k(e)), gt))
