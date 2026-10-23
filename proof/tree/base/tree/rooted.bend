# eukhe: lemmas the proofs of area tree share: tree/rooted

import Base
import ../../../../bend/director.bend as Dr
import ../../../../bend/tree.bend as Tr
import ../../../base/bool.bend as LBool
import ../../../base/logic/bool.bend as LLogicBool
import ../../../base/nat.bend as LNat
import ../bool.bend as LABool
import ../list.bend as LAList
import ../logic.bend as LALogic
import ../nat.bend as LANat
import ./has.bend as LATreeHas
import ./ok.bend as LATreeOk

def pt.rooted_mono_set(s: List<&2, Tr.Ent>, +all: List<&2, Tr.Ent>, +e: Tr.Ent, +rs: {Tr.rooted.go(s, all) == True{} : Bool}) -> {Tr.rooted.go(s, Tr.set(all, e)) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +h <> +r:
      +oh = LLogicBool.tree.pt.and_l(Tr.ok(all, Tr.Ent.k(h), Tr.Ent.p(h)), Tr.rooted.go(r, all), rs)
      +rr = LLogicBool.tree.pt.and_r(Tr.ok(all, Tr.Ent.k(h), Tr.Ent.p(h)), Tr.rooted.go(r, all), rs)
      LBool.tree.pt.and_t(Tr.ok(Tr.set(all, e), Tr.Ent.k(h), Tr.Ent.p(h)), Tr.rooted.go(r, Tr.set(all, e)), LATreeOk.pt.ok_set(all, e, Tr.Ent.k(h), Tr.Ent.p(h), oh), pt.rooted_mono_set(r, all, e, rr))

def pt.rooted_set_go(s: List<&2, Tr.Ent>, +all: List<&2, Tr.Ent>, +e: Tr.Ent, c: Cmp, +rs: {Tr.rooted.go(s, all) == True{} : Bool}, +oe: {Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)) == True{} : Bool}) -> {Tr.rooted.go(Tr.set.go(s, e, c), Tr.set(all, e)) == True{} : Bool}:
  match s:
    case Nil{}:
      LBool.tree.pt.and_t(Tr.ok(Tr.set(all, e), Tr.Ent.k(e), Tr.Ent.p(e)), True{}, LATreeOk.pt.ok_set(all, e, Tr.Ent.k(e), Tr.Ent.p(e), oe), {==})
    case +h <> +r:
      match c:
        case LT{}:
          LBool.tree.pt.and_t(Tr.ok(Tr.set(all, e), Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(h <> r, Tr.set(all, e)), LATreeOk.pt.ok_set(all, e, Tr.Ent.k(e), Tr.Ent.p(e), oe), pt.rooted_mono_set(h <> r, all, e, rs))
        case EQ{}:
          LBool.tree.pt.and_t(Tr.ok(Tr.set(all, e), Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(r, Tr.set(all, e)), LATreeOk.pt.ok_set(all, e, Tr.Ent.k(e), Tr.Ent.p(e), oe), pt.rooted_mono_set(r, all, e, LLogicBool.tree.pt.and_r(Tr.ok(all, Tr.Ent.k(h), Tr.Ent.p(h)), Tr.rooted.go(r, all), rs)))
        case GT{}:
          +na = Tr.set(all, e)
          +oh = LLogicBool.tree.pt.and_l(Tr.ok(all, Tr.Ent.k(h), Tr.Ent.p(h)), Tr.rooted.go(r, all), rs)
          +rr = LLogicBool.tree.pt.and_r(Tr.ok(all, Tr.Ent.k(h), Tr.Ent.p(h)), Tr.rooted.go(r, all), rs)
          LBool.tree.pt.and_t(Tr.ok(na, Tr.Ent.k(h), Tr.Ent.p(h)), Tr.rooted.go(Tr.set.go(r, e, Tr.first(Tr.Ent.k(e), r)), na), LATreeOk.pt.ok_set(all, e, Tr.Ent.k(h), Tr.Ent.p(h), oh), pt.rooted_set_go(r, all, e, Tr.first(Tr.Ent.k(e), r), rr, oe))

# the nodes prune keeps hang under the root or under kept nodes
def pt.rooted_prune_go(s: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool, eh: {Tr.gone.at(s, gone) == hit : Bool}, +pre: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +cv: {LALogic.pt.cov(pre, b, gone) == True{} : Bool}, +up: {LALogic.pt.upl(s, pre) == True{} : Bool}) -> {Tr.rooted.go(Tr.prune.go(s, gone, hit), List.append(&2, Tr.Ent, b, Tr.prune.go(s, gone, hit))) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +k = Tr.Ent.k(e)
          +g2 = {k <> gone : List<&2, Nat>}
          +pre2 = List.append(&2, Tr.Ent, pre, [e])
          +c1 = LBool.tree.pt.and_t(Bool.or(Tr.has(b, k), Tr.elem(g2, k)), True{}, LABool.pt.or_tr(Tr.has(b, k), Tr.elem(g2, k), LABool.pt.or_tl(Nat.is_eq(k, k), Tr.elem(gone, k), Equal.sym(Bool, True{}, Nat.is_eq(k, k), LANat.pt.eq_refl(k)))), {==})
          +cv2 = LAList.pt.cov_app(pre, [e], b, g2, LABool.pt.cov_gone(pre, b, gone, k, cv), c1)
          pt.rooted_prune_go(r, g2, Tr.gone.at(r, g2), {==}, pre2, b, cv2, LLogicBool.tree.pt.and_r(Tr.ok(pre, k, Tr.Ent.p(e)), LALogic.pt.upl(r, pre2), up))
        case False{}:
          +k = Tr.Ent.k(e)
          +p = Tr.Ent.p(e)
          +P = Tr.prune.go(r, gone, Tr.gone.at(r, gone))
          +pre2 = List.append(&2, Tr.Ent, pre, [e])
          +b2 = List.append(&2, Tr.Ent, b, [e])
          +ng = LALogic.pt.or_r(Tr.elem(gone, k), Tr.elem(gone, p), eh)
          +ok1 = LATreeOk.pt.ok_keep(pre, b, gone, e <> P, k, p, LLogicBool.tree.pt.and_l(Tr.ok(pre, k, p), LALogic.pt.upl(r, pre2), up), cv, ng)
          +c2 = LBool.tree.pt.and_t(Bool.or(Tr.has(b2, k), Tr.elem(gone, k)), True{}, LABool.pt.or_tl(Tr.has(b2, k), Tr.elem(gone, k), LATreeHas.pt.has_app_r(b, [e], k, LATreeHas.pt.has_head(e, Nil{}))), {==})
          +cv2 = LAList.pt.cov_app(pre, [e], b2, gone, LATreeHas.pt.cov_b(pre, b, [e], gone, cv), c2)
          +ih = pt.rooted_prune_go(r, gone, Tr.gone.at(r, gone), {==}, pre2, b2, cv2, LLogicBool.tree.pt.and_r(Tr.ok(pre, k, p), LALogic.pt.upl(r, pre2), up))
          +eq = LAList.pt.app_snoc(b, e, P)
          +rest = Equal.trans(Bool, Tr.rooted.go(P, List.append(&2, Tr.Ent, b, e <> P)), Tr.rooted.go(P, List.append(&2, Tr.Ent, b2, P)), True{}, Equal.cong(List<&2, Tr.Ent>, Bool, l => Tr.rooted.go(P, l), List.append(&2, Tr.Ent, b, e <> P), List.append(&2, Tr.Ent, b2, P), Equal.sym(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, b2, P), List.append(&2, Tr.Ent, b, e <> P), eq)), ih)
          LBool.tree.pt.and_t(Tr.ok(List.append(&2, Tr.Ent, b, e <> P), k, p), Tr.rooted.go(P, List.append(&2, Tr.Ent, b, e <> P)), ok1, rest)

def pd.rooted_app_all(s: List<&2, Tr.Ent>, +all: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, +rs: {Tr.rooted.go(s, all) == True{} : Bool}) -> {Tr.rooted.go(s, List.append(&2, Tr.Ent, all, C)) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      +he = LLogicBool.tree.pt.and_l(Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(r, all), rs)
      +hr = LLogicBool.tree.pt.and_r(Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(r, all), rs)
      LBool.tree.pt.and_t(Tr.ok(List.append(&2, Tr.Ent, all, C), Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(r, List.append(&2, Tr.Ent, all, C)), LATreeOk.pd.ok_app(all, C, Tr.Ent.k(e), Tr.Ent.p(e), he), pd.rooted_app_all(r, all, C, hr))

def pd.rooted_go_app(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +all: List<&2, Tr.Ent>, +ra: {Tr.rooted.go(A, all) == True{} : Bool}, rb: {Tr.rooted.go(B, all) == True{} : Bool}) -> {Tr.rooted.go(List.append(&2, Tr.Ent, A, B), all) == True{} : Bool}:
  match A:
    case Nil{}:
      rb
    case +e <> +r:
      +he = LLogicBool.tree.pt.and_l(Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(r, all), ra)
      +hr = LLogicBool.tree.pt.and_r(Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(r, all), ra)
      LBool.tree.pt.and_t(Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(List.append(&2, Tr.Ent, r, B), all), he, pd.rooted_go_app(r, B, all, hr, rb))

def pd.enc_rooted(s: List<&2, Dr.Layer>) -> {Tr.rooted(Dr.encode(s)) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case l <> +rest:
      match l:
        case Dr.Layer{+k, +b}:
          +n = List.length(&2, Dr.Layer, rest)
          +E = Dr.encode(rest)
          +x = {Tr.Ent{1n+Nat.double(n), Dr.kind.parent(n), k} : Tr.Ent}
          +y = {Tr.Ent{2n+Nat.double(n), 1n+Nat.double(n), b} : Tr.Ent}
          +X = {[x, y] : List<&2, Tr.Ent>}
          +T = List.append(&2, Tr.Ent, E, X)
          +ra = pd.rooted_app_all(E, E, X, pd.enc_rooted(rest))
          +hy = LBool.tree.pt.and_t(Nat.is_lt(1n+Nat.double(n), 2n+Nat.double(n)), Bool.or(Nat.is_eq(1n+Nat.double(n), 0n), Tr.has(T, 1n+Nat.double(n))), LNat.pd.lt_succ(1n+Nat.double(n)), LABool.pt.or_tr(Nat.is_eq(1n+Nat.double(n), 0n), Tr.has(T, 1n+Nat.double(n)), LATreeHas.pt.has_app_r(E, X, 1n+Nat.double(n), LATreeHas.pt.has_head(x, [y]))))
          +rb = LBool.tree.pt.and_t(Tr.ok(T, 1n+Nat.double(n), Dr.kind.parent(n)), Bool.and(Tr.ok(T, 2n+Nat.double(n), 1n+Nat.double(n)), True{}), LATreeOk.pd.parent_ok(rest, X), LBool.tree.pt.and_t(Tr.ok(T, 2n+Nat.double(n), 1n+Nat.double(n)), True{}, hy, {==}))
          pd.rooted_go_app(E, X, T, ra, rb)
