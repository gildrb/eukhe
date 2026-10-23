# eukhe: lemmas the proofs of area tree share: tree/sorted

import Base
import ../../../../bend/tree.bend as Tr
import ../../../base/bool.bend as LBool
import ../../../base/list.bend as LList
import ../../../base/logic/bool.bend as LLogicBool
import ../../../base/nat.bend as LNat
import ../../../base/tree.bend as LTree
import ../bool.bend as LABool
import ../list.bend as LAList
import ../logic.bend as LALogic
import ../nat.bend as LANat
import ./KMap.bend as LATreeKMap
import ./above.bend as LATreeAbove
import ./get.bend as LATreeGet
import ./gone.bend as LATreeGone
import ./has.bend as LATreeHas
import ./puts.bend as LATreePuts

def pt.sorted_set_go(t: List<&2, Tr.Ent>, +e: Tr.Ent, c: Cmp, ec: {Tr.first(Tr.Ent.k(e), t) == c : Cmp}, +st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.sorted(Tr.set.go(t, e, c)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match c:
        case LT{}:
          LBool.tree.pt.and_t(Nat.is_lt(Tr.Ent.k(e), Tr.Ent.k(h)), Tr.sorted(h <> r), LANat.pt.cmp_lt(Tr.Ent.k(e), Tr.Ent.k(h), ec), st)
        case EQ{}:
          %Equal.sym(Nat, Tr.Ent.k(e), Tr.Ent.k(h), LALogic.pt.cmp_eq(Tr.Ent.k(e), Tr.Ent.k(h), ec)) : {Bool.and(Tr.above(_, r), Tr.sorted(r)) == True{} : Bool}
          st
        case GT{}:
          +s = Tr.set.go(r, e, Tr.first(Tr.Ent.k(e), r))
          +al = LLogicBool.tree.pt.and_l(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st)
          +sr = LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st)
          LBool.tree.pt.and_t(Tr.above(Tr.Ent.k(h), s), Tr.sorted(s), LATreeAbove.pt.above_set_go(r, e, Tr.first(Tr.Ent.k(e), r), Tr.Ent.k(h), al, LANat.pt.cmp_gt(Tr.Ent.k(e), Tr.Ent.k(h), ec)), pt.sorted_set_go(r, e, Tr.first(Tr.Ent.k(e), r), {==}, sr))

def pt.sorted_unset_go(t: List<&2, Tr.Ent>, +x: Nat, hit: Bool, +st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.sorted(Tr.unset.go(t, x, hit)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match hit:
        case True{}:
          pt.sorted_unset_go(r, x, Tr.key.at(r, x), LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st))
        case False{}:
          +sr = LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st)
          +u = Tr.unset.go(r, x, Tr.key.at(r, x))
          LBool.tree.pt.and_t(Tr.above(Tr.Ent.k(h), u), Tr.sorted(u), LATreeAbove.pt.above_unset_go(r, x, Tr.key.at(r, x), Tr.Ent.k(h), LLogicBool.tree.pt.and_l(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st), sr), pt.sorted_unset_go(r, x, Tr.key.at(r, x), sr))

def pt.sorted_exact(+t: List<&2, Tr.Ent>, o: Tr.Op, st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.sorted(Tr.exact(t, o)) == True{} : Bool}:
  match o:
    case Tr.Put{+k, +p, +v}:
      pt.sorted_set_go(t, Tr.Ent{k, p, v}, Tr.first(k, t), {==}, st)
    case Tr.Del{+x}:
      pt.sorted_unset_go(t, x, Tr.key.at(t, x), st)

def pt.sorted_patch(ops: List<&2, Tr.Op>, +t: List<&2, Tr.Ent>, st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.sorted(Tr.patch(ops, t)) == True{} : Bool}:
  match ops:
    case Nil{}:
      st
    case +o <> rest:
      pt.sorted_patch(rest, Tr.exact(t, o), pt.sorted_exact(t, o, st))

def pt.sorted_app_r(A: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, st: {Tr.sorted(List.append(&2, Tr.Ent, A, C)) == True{} : Bool}) -> {Tr.sorted(C) == True{} : Bool}:
  match A:
    case Nil{}:
      st
    case +a <> +r:
      pt.sorted_app_r(r, C, LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(a), List.append(&2, Tr.Ent, r, C)), Tr.sorted(List.append(&2, Tr.Ent, r, C)), st))

def pt.sorted_prune_go(t: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool, +st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.sorted(Tr.prune.go(t, gone, hit)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match hit:
        case True{}:
          +g2 = {Tr.Ent.k(h) <> gone : List<&2, Nat>}
          pt.sorted_prune_go(r, g2, Tr.gone.at(r, g2), LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st))
        case False{}:
          +sr = LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st)
          +u = Tr.prune.go(r, gone, Tr.gone.at(r, gone))
          LBool.tree.pt.and_t(Tr.above(Tr.Ent.k(h), u), Tr.sorted(u), LATreeAbove.pt.above_prune_go(r, gone, Tr.gone.at(r, gone), Tr.Ent.k(h), LLogicBool.tree.pt.and_l(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st), sr), pt.sorted_prune_go(r, gone, Tr.gone.at(r, gone), sr))

def pt.upl_of(s: List<&2, Tr.Ent>, +pre: List<&2, Tr.Ent>, +rs: {Tr.rooted.go(s, List.append(&2, Tr.Ent, pre, s)) == True{} : Bool}, +st: {Tr.sorted(List.append(&2, Tr.Ent, pre, s)) == True{} : Bool}) -> {LALogic.pt.upl(s, pre) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      +k = Tr.Ent.k(e)
      +p = Tr.Ent.p(e)
      +X = {e <> r : List<&2, Tr.Ent>}
      +A = List.append(&2, Tr.Ent, pre, X)
      +pre2 = List.append(&2, Tr.Ent, pre, [e])
      +oA = LLogicBool.tree.pt.and_l(Tr.ok(A, k, p), Tr.rooted.go(r, A), rs)
      +lt = LLogicBool.tree.pt.and_l(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(A, p)), oA)
      +hx = LATreeHas.pt.has_below(X, p, lt, pt.sorted_app_r(pre, X, st))
      +hp = Equal.trans(Bool, Tr.has(A, p), Bool.or(Tr.has(pre, p), Tr.has(X, p)), Tr.has(pre, p), LATreeHas.pt.has_app(pre, X, p), Equal.trans(Bool, Bool.or(Tr.has(pre, p), Tr.has(X, p)), Bool.or(Tr.has(pre, p), False{}), Tr.has(pre, p), Equal.cong(Bool, Bool, z => Bool.or(Tr.has(pre, p), z), Tr.has(X, p), False{}, hx), LABool.tree.pt.or_false_r(Tr.has(pre, p))))
      +okp = Equal.trans(Bool, Tr.ok(pre, k, p), Tr.ok(A, k, p), True{}, Equal.cong(Bool, Bool, z => Bool.and(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), z)), Tr.has(pre, p), Tr.has(A, p), Equal.sym(Bool, Tr.has(A, p), Tr.has(pre, p), hp)), oA)
      +eq = LAList.pt.app_snoc(pre, e, r)
      +rs2 = Equal.trans(Bool, Tr.rooted.go(r, List.append(&2, Tr.Ent, pre2, r)), Tr.rooted.go(r, A), True{}, Equal.cong(List<&2, Tr.Ent>, Bool, l => Tr.rooted.go(r, l), List.append(&2, Tr.Ent, pre2, r), A, eq), LLogicBool.tree.pt.and_r(Tr.ok(A, k, p), Tr.rooted.go(r, A), rs))
      +st2 = Equal.trans(Bool, Tr.sorted(List.append(&2, Tr.Ent, pre2, r)), Tr.sorted(A), True{}, Equal.cong(List<&2, Tr.Ent>, Bool, l => Tr.sorted(l), List.append(&2, Tr.Ent, pre2, r), A, eq), st)
      LBool.tree.pt.and_t(Tr.ok(pre, k, p), LALogic.pt.upl(r, pre2), okp, pt.upl_of(r, pre2, rs2, st2))

def rewind_reaches(+a: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, ga: {Tr.sound(a) == True{} : Bool}, +gb: {Tr.sound(b) == True{} : Bool}) -> {Tr.apply(a, Tr.Rewind{Tr.diff(a, b)}) == b : List<&2, Tr.Ent>}:
  +n = Tr.patch(Tr.diff(a, b), a)
  +sb = LLogicBool.tree.pt.and_l(Tr.sorted(b), Tr.rooted(b), gb)
  +sn = pt.sorted_patch(Tr.diff(a, b), a, LLogicBool.tree.pt.and_l(Tr.sorted(a), Tr.rooted(a), ga))
  +eq = LATreeGet.pt.ext(n, b, sn, sb, LATreePuts.pt.agree_reach(n, a, b, sb), LATreePuts.pt.agree_reach(b, a, b, sb))
  %Equal.sym(List<&2, Tr.Ent>, n, b, eq) : {Tr.keep.at(Tr.sound(_), a, _) == b : List<&2, Tr.Ent>}
  %Equal.sym(Bool, Tr.sound(b), True{}, gb) : {Tr.keep.at(_, a, b) == b : List<&2, Tr.Ent>}
  {==}

def tc.sorted_app(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +sa: {Tr.sorted(A) == True{} : Bool}, +sb: {Tr.sorted(B) == True{} : Bool}, +la: {LLogicBool.tc.lt(A, b) == True{} : Bool}, +gb: {LLogicBool.tc.ge(B, b) == True{} : Bool}) -> {Tr.sorted(List.append(&2, Tr.Ent, A, B)) == True{} : Bool}:
  match A:
    case Nil{}:
      sb
    case +e <> +r:
      +ar = LLogicBool.tree.pt.and_l(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), sa)
      +sr = LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), sa)
      +R = List.append(&2, Tr.Ent, r, B)
      LBool.tree.pt.and_t(Tr.above(Tr.Ent.k(e), R), Tr.sorted(R), LATreeAbove.tc.above_app(Tr.Ent.k(e), r, B, b, ar, LNat.tc.lt_head(e, r, b, la), gb), tc.sorted_app(r, B, b, sr, sb, LLogicBool.tc.lt_tail(e, r, b, la), gb))

# The key map: order, lookup, put, unset

def tc.sorted_read(m: Tr.KMap, +bt: {LLogicBool.tc.bst(m) == True{} : Bool}) -> {Tr.sorted(Tr.KMap.read(m)) == True{} : Bool}:
  match m:
    case Tr.KNil{}:
      {==}
    case Tr.KOne{e}:
      {==}
    case Tr.KFork{+mid, +mp, +l, +r}:
      tc.sorted_app(Tr.KMap.read(l), Tr.KMap.read(r), mid, tc.sorted_read(l, LLogicBool.tc.bst_l(mid, mp, l, r, bt)), tc.sorted_read(r, LBool.tc.bst_r(mid, mp, l, r, bt)), LTree.tc.bst_lt(mid, mp, l, r, bt), LTree.tc.bst_ge(mid, mp, l, r, bt))

# the test of a rewind on the map is sound on the list
def tc.good_rewind(+ops: List<&2, Tr.Op>, +hs: List<&2, Nat>, +m: Tr.KMap, +bt: {LLogicBool.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.hangs(Tr.KMap.onto(Tr.KMap.patch(ops, hs, m), Nil{}), Tr.KMap.patch(ops, hs, m)) == Tr.sound(Tr.patch(ops, Tr.KMap.read(m))) : Bool}:
  +n = Tr.KMap.patch(ops, hs, m)
  +bn = LTree.tc.patch_bst(ops, hs, m, bt)
  +N = Tr.KMap.read(n)
  %Equal.sym(List<&2, Tr.Ent>, Tr.KMap.onto(n, Nil{}), N, LATreeKMap.tc.onto_nil(n)) : {Tr.KMap.hangs(_, n) == Tr.sound(Tr.patch(ops, Tr.KMap.read(m))) : Bool}
  %Equal.sym(Bool, Tr.KMap.hangs(N, n), Tr.rooted.go(N, N), LATreeGet.tc.hangs(N, n, bn)) : {_ == Tr.sound(Tr.patch(ops, Tr.KMap.read(m))) : Bool}
  %LATreeKMap.tc.patch_read(ops, hs, m, bt) : {Tr.rooted.go(N, N) == Tr.sound(_) : Bool}
  %Equal.sym(Bool, Tr.sorted(N), True{}, tc.sorted_read(n, bn)) : {Tr.rooted.go(N, N) == Bool.and(_, Tr.rooted(N)) : Bool}
  {==}

# the keys a delete of x cuts on the map are the keys the walk drops
def tc.del_keys(+m: Tr.KMap, +x: Nat, +bt: {LLogicBool.tc.bst(m) == True{} : Bool}, +mk: {LALogic.tc.mpok(m) == True{} : Bool}, +sd: {Tr.sound(Tr.KMap.read(m)) == True{} : Bool}) -> {LALogic.tc.dgo(Tr.KMap.ups(m, x, Nil{}, Tr.KMap.gl(m, x), Tr.KMap.gr(m, x)), [x], Tr.gone.at(Tr.KMap.ups(m, x, Nil{}, Tr.KMap.gl(m, x), Tr.KMap.gr(m, x)), [x])) == LALogic.tc.dgo(Tr.KMap.read(m), [x], Tr.gone.at(Tr.KMap.read(m), [x])) : List<&2, Nat>}:
  +t = Tr.KMap.read(m)
  +U = Tr.KMap.ups(m, x, Nil{}, Tr.KMap.gl(m, x), Tr.KMap.gr(m, x))
  +rf = Equal.trans(List<&2, Tr.Ent>, U, List.append(&2, Tr.Ent, LALogic.tc.fx(t, x), Nil{}), LALogic.tc.fx(t, x), LATreeKMap.tc.ups_read(m, x, Nil{}, Tr.KMap.gl(m, x), Tr.KMap.gr(m, x), {==}, {==}, bt, mk), LList.tc.app_nil(LALogic.tc.fx(t, x)))
  +ng = LBool.tree.pt.and_t(Bool.not(Nat.is_lt(x, x)), True{}, LBool.pt.not_t(Nat.is_lt(x, x), LNat.pt.lt_irrefl(x)), {==})
  +g = LBool.tree.pt.and_t(Bool.or(Nat.is_eq(x, x), Tr.above(x, t)), True{}, LABool.pt.or_tl(Nat.is_eq(x, x), Tr.above(x, t), Equal.sym(Bool, True{}, Nat.is_eq(x, x), LANat.pt.eq_refl(x))), {==})
  +dk = LALogic.tc.desc_of(t, t, LLogicBool.tree.pt.and_r(Tr.sorted(t), Tr.rooted(t), sd))
  %Equal.sym(List<&2, Tr.Ent>, U, LALogic.tc.fx(t, x), rf) : {LALogic.tc.dgo(_, [x], Tr.gone.at(_, [x])) == LALogic.tc.dgo(t, [x], Tr.gone.at(t, [x])) : List<&2, Nat>}
  Equal.sym(List<&2, Nat>, LALogic.tc.dgo(t, [x], Tr.gone.at(t, [x])), LALogic.tc.dgo(LALogic.tc.fx(t, x), [x], Tr.gone.at(LALogic.tc.fx(t, x), [x])), LATreeGone.tc.drops_fx(t, [x], Tr.gone.at(t, [x]), {==}, x, ng, g, tc.sorted_read(m, bt), dk))

# a sorted list, then sorted nodes above all its keys, is sorted
def pd.sorted_snoc(A: List<&2, Tr.Ent>, +x: Tr.Ent, +C: List<&2, Tr.Ent>, +sa: {Tr.sorted(A) == True{} : Bool}, sc: {Tr.sorted(x <> C) == True{} : Bool}, +la: {LALogic.pd.lt_all(A, Tr.Ent.k(x)) == True{} : Bool}) -> {Tr.sorted(List.append(&2, Tr.Ent, A, x <> C)) == True{} : Bool}:
  match A:
    case Nil{}:
      sc
    case +e <> +r:
      +sr = LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), sa)
      +lr = LLogicBool.tree.pt.and_r(Nat.is_lt(Tr.Ent.k(e), Tr.Ent.k(x)), LALogic.pd.lt_all(r, Tr.Ent.k(x)), la)
      LBool.tree.pt.and_t(Tr.above(Tr.Ent.k(e), List.append(&2, Tr.Ent, r, x <> C)), Tr.sorted(List.append(&2, Tr.Ent, r, x <> C)), LATreeAbove.pd.above_app(e, r, x, C, sa, la), pd.sorted_snoc(r, x, C, sr, sc, lr))
