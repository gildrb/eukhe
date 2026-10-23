# eukhe: lemmas the proofs of area tree share: tree/KMap

import Base
import ../../../../bend/tree.bend as Tr
import ../../../base/bool.bend as LBool
import ../../../base/list.bend as LList
import ../../../base/logic/bool.bend as LLogicBool
import ../../../base/logic/logic.bend as LLogicLogic
import ../../../base/tree.bend as LTree
import ../bool.bend as LABool
import ../list.bend as LAList
import ../logic.bend as LALogic
import ../nat.bend as LANat

# the entry points

def tc.set_read(+m: Tr.KMap, +hs: List<&2, Nat>, +e: Tr.Ent, +bt: {LLogicBool.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.read(Tr.KMap.set(m, hs, e)) == Tr.set(Tr.KMap.read(m), e) : List<&2, Tr.Ent>}:
  LTree.tc.put_read(m, hs, 0n, e, Tr.KMap.at(m, Tr.Ent.k(e)), {==}, bt)

def tc.del_read(+m: Tr.KMap, +x: Nat, +bt: {LLogicBool.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.read(Tr.KMap.del(m, x)) == Tr.unset(Tr.KMap.read(m), x) : List<&2, Tr.Ent>}:
  LTree.tc.unset_read(m, x, Tr.KMap.at(m, x), {==}, bt)

def tc.drop_read(ks: List<&2, Nat>, +m: Tr.KMap, +bt: {LLogicBool.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.read(Tr.KMap.drop(ks, m)) == LALogic.tc.unsets(ks, Tr.KMap.read(m)) : List<&2, Tr.Ent>}:
  match ks:
    case Nil{}:
      {==}
    case +k <> rest:
      +D = Tr.KMap.del(m, k)
      +ih = tc.drop_read(rest, D, LTree.tc.del_bst(m, k, bt))
      %tc.del_read(m, k, bt) : {Tr.KMap.read(Tr.KMap.drop(rest, D)) == LALogic.tc.unsets(rest, _) : List<&2, Tr.Ent>}
      ih

def tc.mpok_fork(+mid: Nat, +l: Tr.KMap, +r: Tr.KMap, +ml: {LALogic.tc.mpok(l) == True{} : Bool}, +mr: {LALogic.tc.mpok(r) == True{} : Bool}) -> {LALogic.tc.mpok(Tr.KMap.fork(mid, l, r)) == True{} : Bool}:
  +a = Tr.KMap.mp(l)
  +b = Tr.KMap.mp(r)
  +M = Nat.max(a, b)
  LBool.tree.pt.and_t(LALogic.tc.mpok(l), Bool.and(LALogic.tc.mpok(r), Bool.and(Nat.is_ge(M, a), Nat.is_ge(M, b))), ml, LBool.tree.pt.and_t(LALogic.tc.mpok(r), Bool.and(Nat.is_ge(M, a), Nat.is_ge(M, b)), mr, LBool.tree.pt.and_t(Nat.is_ge(M, a), Nat.is_ge(M, b), Nat.max_ge_l(a, b), Nat.max_ge_r(a, b))))

def tc.split_mpok(+a: Tr.Ent, +b: Tr.Ent, c: Bool) -> {LALogic.tc.mpok(Tr.KMap.split(a, b, c)) == True{} : Bool}:
  match c:
    case True{}:
      tc.mpok_fork(Tr.Ent.k(b), Tr.KOne{a}, Tr.KOne{b}, {==}, {==})
    case False{}:
      tc.mpok_fork(Tr.Ent.k(a), Tr.KOne{b}, Tr.KOne{a}, {==}, {==})

def tc.two_mpok(hs: List<&2, Nat>, +lo: Nat, +a: Tr.Ent, +b: Tr.Ent, ca: Bool, cb: Bool) -> {LALogic.tc.mpok(Tr.KMap.two(hs, lo, a, b, ca, cb)) == True{} : Bool}:
  match hs:
    case Nil{}:
      tc.split_mpok(a, b, Nat.is_lt(Tr.Ent.k(a), Tr.Ent.k(b)))
    case +h <> +rest:
      match ca cb:
        case True{} True{}:
          +g = Tr.KMap.half(rest)
          +X = Tr.KMap.two(rest, lo, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(lo, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(lo, g)))
          tc.mpok_fork(Nat.add(lo, h), X, Tr.KNil{}, tc.two_mpok(rest, lo, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(lo, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(lo, g))), {==})
        case True{} False{}:
          tc.mpok_fork(Nat.add(lo, h), Tr.KOne{a}, Tr.KOne{b}, {==}, {==})
        case False{} True{}:
          tc.mpok_fork(Nat.add(lo, h), Tr.KOne{b}, Tr.KOne{a}, {==}, {==})
        case False{} False{}:
          +g = Tr.KMap.half(rest)
          +n = Nat.add(lo, h)
          +X = Tr.KMap.two(rest, n, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(n, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(n, g)))
          tc.mpok_fork(n, Tr.KNil{}, X, {==}, tc.two_mpok(rest, n, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(n, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(n, g))))

def tc.put_mpok(m: Tr.KMap, +hs: List<&2, Nat>, +lo: Nat, +e: Tr.Ent, b: Bool, +mk: {LALogic.tc.mpok(m) == True{} : Bool}) -> {LALogic.tc.mpok(Tr.KMap.put(m, hs, lo, e, b)) == True{} : Bool}:
  match m b:
    case Tr.KNil{} True{}:
      {==}
    case Tr.KNil{} False{}:
      {==}
    case Tr.KOne{+f} True{}:
      {==}
    case Tr.KOne{+f} False{}:
      tc.two_mpok(hs, lo, f, e, Nat.is_lt(Tr.Ent.k(f), Nat.add(lo, Tr.KMap.half(hs))), Nat.is_lt(Tr.Ent.k(e), Nat.add(lo, Tr.KMap.half(hs))))
    case Tr.KFork{+mid, +mp, +l, +r} True{}:
      +P = Tr.KMap.put(l, Tr.KMap.below(hs), lo, e, Tr.KMap.at(l, Tr.Ent.k(e)))
      tc.mpok_fork(mid, P, r, tc.put_mpok(l, Tr.KMap.below(hs), lo, e, Tr.KMap.at(l, Tr.Ent.k(e)), LALogic.tc.mpok_l(mid, mp, l, r, mk)), LABool.tc.mpok_r(mid, mp, l, r, mk))
    case Tr.KFork{+mid, +mp, +l, +r} False{}:
      +P = Tr.KMap.put(r, Tr.KMap.below(hs), mid, e, Tr.KMap.at(r, Tr.Ent.k(e)))
      tc.mpok_fork(mid, l, P, LALogic.tc.mpok_l(mid, mp, l, r, mk), tc.put_mpok(r, Tr.KMap.below(hs), mid, e, Tr.KMap.at(r, Tr.Ent.k(e)), LABool.tc.mpok_r(mid, mp, l, r, mk)))

def tc.unset_mpok(m: Tr.KMap, +x: Nat, b: Bool, +mk: {LALogic.tc.mpok(m) == True{} : Bool}) -> {LALogic.tc.mpok(Tr.KMap.unset(m, x, b)) == True{} : Bool}:
  match m b:
    case Tr.KNil{} True{}:
      {==}
    case Tr.KNil{} False{}:
      {==}
    case Tr.KOne{+e} True{}:
      {==}
    case Tr.KOne{+e} False{}:
      {==}
    case Tr.KFork{+mid, +mp, +l, +r} True{}:
      +U = Tr.KMap.unset(l, x, Tr.KMap.at(l, x))
      tc.mpok_fork(mid, U, r, tc.unset_mpok(l, x, Tr.KMap.at(l, x), LALogic.tc.mpok_l(mid, mp, l, r, mk)), LABool.tc.mpok_r(mid, mp, l, r, mk))
    case Tr.KFork{+mid, +mp, +l, +r} False{}:
      +U = Tr.KMap.unset(r, x, Tr.KMap.at(r, x))
      tc.mpok_fork(mid, l, U, LALogic.tc.mpok_l(mid, mp, l, r, mk), tc.unset_mpok(r, x, Tr.KMap.at(r, x), LABool.tc.mpok_r(mid, mp, l, r, mk)))

def tc.set_mpok(+m: Tr.KMap, +hs: List<&2, Nat>, +e: Tr.Ent, +mk: {LALogic.tc.mpok(m) == True{} : Bool}) -> {LALogic.tc.mpok(Tr.KMap.set(m, hs, e)) == True{} : Bool}:
  tc.put_mpok(m, hs, 0n, e, Tr.KMap.at(m, Tr.Ent.k(e)), mk)

def tc.del_mpok(+m: Tr.KMap, +x: Nat, +mk: {LALogic.tc.mpok(m) == True{} : Bool}) -> {LALogic.tc.mpok(Tr.KMap.del(m, x)) == True{} : Bool}:
  tc.unset_mpok(m, x, Tr.KMap.at(m, x), mk)

def tc.drop_mpok(ks: List<&2, Nat>, +m: Tr.KMap, +mk: {LALogic.tc.mpok(m) == True{} : Bool}) -> {LALogic.tc.mpok(Tr.KMap.drop(ks, m)) == True{} : Bool}:
  match ks:
    case Nil{}:
      mk
    case +k <> rest:
      tc.drop_mpok(rest, Tr.KMap.del(m, k), tc.del_mpok(m, k, mk))

# every parent of the map is at most its largest parent key
def tc.mp_ple(m: Tr.KMap, +mk: {LALogic.tc.mpok(m) == True{} : Bool}) -> {LALogic.tc.ple(Tr.KMap.read(m), Tr.KMap.mp(m)) == True{} : Bool}:
  match m:
    case Tr.KNil{}:
      {==}
    case Tr.KOne{+e}:
      LBool.tree.pt.and_t(Nat.is_ge(Tr.Ent.p(e), Tr.Ent.p(e)), True{}, Nat.ge_refl(Tr.Ent.p(e)), {==})
    case Tr.KFork{+mid, +mp, +l, +r}:
      +pl = LANat.tc.ple_mono(Tr.KMap.read(l), Tr.KMap.mp(l), mp, tc.mp_ple(l, LALogic.tc.mpok_l(mid, mp, l, r, mk)), LANat.tc.mpok_gl(mid, mp, l, r, mk))
      +pr = LANat.tc.ple_mono(Tr.KMap.read(r), Tr.KMap.mp(r), mp, tc.mp_ple(r, LABool.tc.mpok_r(mid, mp, l, r, mk)), LANat.tc.mpok_gr(mid, mp, l, r, mk))
      LAList.tc.ple_app(Tr.KMap.read(l), Tr.KMap.read(r), mp, pl, pr)

def tc.ups_read(m: Tr.KMap, +x: Nat, +acc: List<&2, Tr.Ent>, gl: Bool, gr: Bool, +egl: {Tr.KMap.gl(m, x) == gl : Bool}, +egr: {Tr.KMap.gr(m, x) == gr : Bool}, +bt: {LLogicBool.tc.bst(m) == True{} : Bool}, +mk: {LALogic.tc.mpok(m) == True{} : Bool}) -> {Tr.KMap.ups(m, x, acc, gl, gr) == List.append(&2, Tr.Ent, LALogic.tc.fx(Tr.KMap.read(m), x), acc) : List<&2, Tr.Ent>}:
  match m gl gr:
    case Tr.KNil{} True{} True{}:
      {==}
    case Tr.KNil{} True{} False{}:
      {==}
    case Tr.KNil{} False{} True{}:
      {==}
    case Tr.KNil{} False{} False{}:
      {==}
    case Tr.KOne{+e} True{} True{}:
      %Equal.sym(Bool, Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x))), True{}, egl) : {e <> acc == List.append(&2, Tr.Ent, LALogic.tc.fx.at(_, e, Nil{}), acc) : List<&2, Tr.Ent>}
      {==}
    case Tr.KOne{+e} True{} False{}:
      %Equal.sym(Bool, Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x))), True{}, egl) : {e <> acc == List.append(&2, Tr.Ent, LALogic.tc.fx.at(_, e, Nil{}), acc) : List<&2, Tr.Ent>}
      {==}
    case Tr.KOne{+e} False{} True{}:
      %Equal.sym(Bool, Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x))), False{}, egl) : {acc == List.append(&2, Tr.Ent, LALogic.tc.fx.at(_, e, Nil{}), acc) : List<&2, Tr.Ent>}
      {==}
    case Tr.KOne{+e} False{} False{}:
      %Equal.sym(Bool, Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x))), False{}, egl) : {acc == List.append(&2, Tr.Ent, LALogic.tc.fx.at(_, e, Nil{}), acc) : List<&2, Tr.Ent>}
      {==}
    case Tr.KFork{+mid, +mp, +l, +r} True{} True{}:
      +L = Tr.KMap.read(l)
      +R = Tr.KMap.read(r)
      +ir = tc.ups_read(r, x, acc, Tr.KMap.gl(r, x), Tr.KMap.gr(r, x), {==}, {==}, LBool.tc.bst_r(mid, mp, l, r, bt), LABool.tc.mpok_r(mid, mp, l, r, mk))
      +il = tc.ups_read(l, x, List.append(&2, Tr.Ent, LALogic.tc.fx(R, x), acc), Tr.KMap.gl(l, x), Tr.KMap.gr(l, x), {==}, {==}, LLogicBool.tc.bst_l(mid, mp, l, r, bt), LALogic.tc.mpok_l(mid, mp, l, r, mk))
      %Equal.sym(List<&2, Tr.Ent>, Tr.KMap.ups(r, x, acc, Tr.KMap.gl(r, x), Tr.KMap.gr(r, x)), List.append(&2, Tr.Ent, LALogic.tc.fx(R, x), acc), ir) : {Tr.KMap.ups(l, x, _, Tr.KMap.gl(l, x), Tr.KMap.gr(l, x)) == List.append(&2, Tr.Ent, LALogic.tc.fx(List.append(&2, Tr.Ent, L, R), x), acc) : List<&2, Tr.Ent>}
      %Equal.sym(List<&2, Tr.Ent>, LALogic.tc.fx(List.append(&2, Tr.Ent, L, R), x), List.append(&2, Tr.Ent, LALogic.tc.fx(L, x), LALogic.tc.fx(R, x)), LAList.tc.fx_app(L, R, x)) : {Tr.KMap.ups(l, x, List.append(&2, Tr.Ent, LALogic.tc.fx(R, x), acc), Tr.KMap.gl(l, x), Tr.KMap.gr(l, x)) == List.append(&2, Tr.Ent, _, acc) : List<&2, Tr.Ent>}
      %Equal.sym(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, LALogic.tc.fx(L, x), LALogic.tc.fx(R, x)), acc), List.append(&2, Tr.Ent, LALogic.tc.fx(L, x), List.append(&2, Tr.Ent, LALogic.tc.fx(R, x), acc)), LAList.tc.app_assoc(LALogic.tc.fx(L, x), LALogic.tc.fx(R, x), acc)) : {Tr.KMap.ups(l, x, List.append(&2, Tr.Ent, LALogic.tc.fx(R, x), acc), Tr.KMap.gl(l, x), Tr.KMap.gr(l, x)) == _ : List<&2, Tr.Ent>}
      il
    case Tr.KFork{+mid, +mp, +l, +r} True{} False{}:
      +L = Tr.KMap.read(l)
      +R = Tr.KMap.read(r)
      +xm = LALogic.tc.not_ff(Nat.is_lt(x, mid), LALogic.tc.or_fl(Bool.not(Nat.is_lt(x, mid)), Bool.not(Nat.is_lt(Tr.KMap.mp(r), x)), egr))
      +rx = LALogic.tc.not_ff(Nat.is_lt(Tr.KMap.mp(r), x), LALogic.pt.or_r(Bool.not(Nat.is_lt(x, mid)), Bool.not(Nat.is_lt(Tr.KMap.mp(r), x)), egr))
      +nr = LANat.tc.fx_nil(R, x, Tr.KMap.mp(r), LALogic.tc.nokey_ge(R, mid, x, LTree.tc.bst_ge(mid, mp, l, r, bt), xm), tc.mp_ple(r, LABool.tc.mpok_r(mid, mp, l, r, mk)), rx)
      +il = tc.ups_read(l, x, acc, Tr.KMap.gl(l, x), Tr.KMap.gr(l, x), {==}, {==}, LLogicBool.tc.bst_l(mid, mp, l, r, bt), LALogic.tc.mpok_l(mid, mp, l, r, mk))
      %Equal.sym(List<&2, Tr.Ent>, LALogic.tc.fx(List.append(&2, Tr.Ent, L, R), x), List.append(&2, Tr.Ent, LALogic.tc.fx(L, x), LALogic.tc.fx(R, x)), LAList.tc.fx_app(L, R, x)) : {Tr.KMap.ups(l, x, acc, Tr.KMap.gl(l, x), Tr.KMap.gr(l, x)) == List.append(&2, Tr.Ent, _, acc) : List<&2, Tr.Ent>}
      %Equal.sym(List<&2, Tr.Ent>, LALogic.tc.fx(R, x), Nil{}, nr) : {Tr.KMap.ups(l, x, acc, Tr.KMap.gl(l, x), Tr.KMap.gr(l, x)) == List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, LALogic.tc.fx(L, x), _), acc) : List<&2, Tr.Ent>}
      %Equal.sym(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, LALogic.tc.fx(L, x), Nil{}), LALogic.tc.fx(L, x), LList.tc.app_nil(LALogic.tc.fx(L, x))) : {Tr.KMap.ups(l, x, acc, Tr.KMap.gl(l, x), Tr.KMap.gr(l, x)) == List.append(&2, Tr.Ent, _, acc) : List<&2, Tr.Ent>}
      il
    case Tr.KFork{+mid, +mp, +l, +r} False{} True{}:
      +L = Tr.KMap.read(l)
      +R = Tr.KMap.read(r)
      +xm = LALogic.pt.or_l(Nat.is_lt(x, mid), Bool.not(Nat.is_lt(Tr.KMap.mp(l), x)), egl)
      +lx = LALogic.tc.not_ff(Nat.is_lt(Tr.KMap.mp(l), x), LALogic.pt.or_r(Nat.is_lt(x, mid), Bool.not(Nat.is_lt(Tr.KMap.mp(l), x)), egl))
      +nl = LANat.tc.fx_nil(L, x, Tr.KMap.mp(l), LALogic.tc.nokey_lt(L, mid, x, LTree.tc.bst_lt(mid, mp, l, r, bt), xm), tc.mp_ple(l, LALogic.tc.mpok_l(mid, mp, l, r, mk)), lx)
      +ir = tc.ups_read(r, x, acc, Tr.KMap.gl(r, x), Tr.KMap.gr(r, x), {==}, {==}, LBool.tc.bst_r(mid, mp, l, r, bt), LABool.tc.mpok_r(mid, mp, l, r, mk))
      %Equal.sym(List<&2, Tr.Ent>, LALogic.tc.fx(List.append(&2, Tr.Ent, L, R), x), List.append(&2, Tr.Ent, LALogic.tc.fx(L, x), LALogic.tc.fx(R, x)), LAList.tc.fx_app(L, R, x)) : {Tr.KMap.ups(r, x, acc, Tr.KMap.gl(r, x), Tr.KMap.gr(r, x)) == List.append(&2, Tr.Ent, _, acc) : List<&2, Tr.Ent>}
      %Equal.sym(List<&2, Tr.Ent>, LALogic.tc.fx(L, x), Nil{}, nl) : {Tr.KMap.ups(r, x, acc, Tr.KMap.gl(r, x), Tr.KMap.gr(r, x)) == List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, _, LALogic.tc.fx(R, x)), acc) : List<&2, Tr.Ent>}
      ir
    case Tr.KFork{+mid, +mp, +l, +r} False{} False{}:
      +L = Tr.KMap.read(l)
      +R = Tr.KMap.read(r)
      +xm = LALogic.pt.or_l(Nat.is_lt(x, mid), Bool.not(Nat.is_lt(Tr.KMap.mp(l), x)), egl)
      +lx = LALogic.tc.not_ff(Nat.is_lt(Tr.KMap.mp(l), x), LALogic.pt.or_r(Nat.is_lt(x, mid), Bool.not(Nat.is_lt(Tr.KMap.mp(l), x)), egl))
      +rx = LALogic.tc.not_ff(Nat.is_lt(Tr.KMap.mp(r), x), LALogic.pt.or_r(Bool.not(Nat.is_lt(x, mid)), Bool.not(Nat.is_lt(Tr.KMap.mp(r), x)), egr))
      +xm2 = LALogic.tc.not_ff(Nat.is_lt(x, mid), LALogic.tc.or_fl(Bool.not(Nat.is_lt(x, mid)), Bool.not(Nat.is_lt(Tr.KMap.mp(r), x)), egr))
      LLogicLogic.pt.absurd({acc == List.append(&2, Tr.Ent, LALogic.tc.fx(List.append(&2, Tr.Ent, L, R), x), acc) : List<&2, Tr.Ent>}, Equal.trans(Bool, True{}, Nat.is_lt(x, mid), False{}, Equal.sym(Bool, Nat.is_lt(x, mid), True{}, xm2), xm))

# A record on the map

def tc.onto(m: Tr.KMap, +acc: List<&2, Tr.Ent>) -> {Tr.KMap.onto(m, acc) == List.append(&2, Tr.Ent, Tr.KMap.read(m), acc) : List<&2, Tr.Ent>}:
  match m:
    case Tr.KNil{}:
      {==}
    case Tr.KOne{e}:
      {==}
    case Tr.KFork{mid, mp, +l, +r}:
      +L = Tr.KMap.read(l)
      +R = Tr.KMap.read(r)
      %Equal.sym(List<&2, Tr.Ent>, Tr.KMap.onto(r, acc), List.append(&2, Tr.Ent, R, acc), tc.onto(r, acc)) : {Tr.KMap.onto(l, _) == List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, L, R), acc) : List<&2, Tr.Ent>}
      %Equal.sym(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, L, R), acc), List.append(&2, Tr.Ent, L, List.append(&2, Tr.Ent, R, acc)), LAList.tc.app_assoc(L, R, acc)) : {Tr.KMap.onto(l, List.append(&2, Tr.Ent, R, acc)) == _ : List<&2, Tr.Ent>}
      tc.onto(l, List.append(&2, Tr.Ent, R, acc))

def tc.onto_nil(+m: Tr.KMap) -> {Tr.KMap.onto(m, Nil{}) == Tr.KMap.read(m) : List<&2, Tr.Ent>}:
  Equal.trans(List<&2, Tr.Ent>, Tr.KMap.onto(m, Nil{}), List.append(&2, Tr.Ent, Tr.KMap.read(m), Nil{}), Tr.KMap.read(m), tc.onto(m, Nil{}), LList.tc.app_nil(Tr.KMap.read(m)))

def tc.exact_read(+m: Tr.KMap, +hs: List<&2, Nat>, o: Tr.Op, +bt: {LLogicBool.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.read(Tr.KMap.exact(m, hs, o)) == Tr.exact(Tr.KMap.read(m), o) : List<&2, Tr.Ent>}:
  match o:
    case Tr.Put{+k, +p, +v}:
      tc.set_read(m, hs, Tr.Ent{k, p, v}, bt)
    case Tr.Del{+x}:
      tc.del_read(m, x, bt)

def tc.patch_read(ops: List<&2, Tr.Op>, +hs: List<&2, Nat>, +m: Tr.KMap, +bt: {LLogicBool.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.read(Tr.KMap.patch(ops, hs, m)) == Tr.patch(ops, Tr.KMap.read(m)) : List<&2, Tr.Ent>}:
  match ops:
    case Nil{}:
      {==}
    case +o <> rest:
      +E = Tr.KMap.exact(m, hs, o)
      %tc.exact_read(m, hs, o, bt) : {Tr.KMap.read(Tr.KMap.patch(rest, hs, E)) == Tr.patch(rest, _) : List<&2, Tr.Ent>}
      tc.patch_read(rest, hs, E, LTree.tc.exact_bst(m, hs, o, bt))

def tc.put_case(b: Bool, +m: Tr.KMap, +hs: List<&2, Nat>, +e: Tr.Ent, +bt: {LLogicBool.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.read(Pair.fst(Tr.KMap, Tr.Ans, Tr.put.ans(b, m, hs, e))) == Tr.put.at(b, Tr.KMap.read(m), e) : List<&2, Tr.Ent>}:
  match b:
    case True{}:
      tc.set_read(m, hs, e, bt)
    case False{}:
      {==}

def tc.keep_case(b: Bool, +m: Tr.KMap, +n: Tr.KMap, +N: List<&2, Tr.Ent>, +rn: {Tr.KMap.read(n) == N : List<&2, Tr.Ent>}) -> {Tr.KMap.read(Pair.fst(Tr.KMap, Tr.Ans, Tr.keep.ans(b, m, n))) == Tr.keep.at(b, Tr.KMap.read(m), N) : List<&2, Tr.Ent>}:
  match b:
    case True{}:
      rn
    case False{}:
      {==}

# a key joins the gone map as it joins the gone list
def tc.gone_of(+hs: List<&2, Nat>, +g: Tr.KMap, +gone: List<&2, Nat>, +k: Nat, +bt: {LLogicBool.tc.bst(g) == True{} : Bool}, +rg: {Tr.KMap.read(g) == LALogic.tc.bld(gone) : List<&2, Tr.Ent>}) -> {Tr.KMap.read(Tr.gone.of(hs, g, k)) == LALogic.tc.bld(k <> gone) : List<&2, Tr.Ent>}:
  Equal.trans(List<&2, Tr.Ent>, Tr.KMap.read(Tr.KMap.set(g, hs, Tr.Ent{k, 0n, 0n})), Tr.set(Tr.KMap.read(g), Tr.Ent{k, 0n, 0n}), LALogic.tc.bld(k <> gone), tc.set_read(g, hs, Tr.Ent{k, 0n, 0n}, bt), Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, z => Tr.set(z, Tr.Ent{k, 0n, 0n}), Tr.KMap.read(g), LALogic.tc.bld(gone), rg))

def tc.exact_mpok(+m: Tr.KMap, +hs: List<&2, Nat>, o: Tr.Op, +mk: {LALogic.tc.mpok(m) == True{} : Bool}) -> {LALogic.tc.mpok(Tr.KMap.exact(m, hs, o)) == True{} : Bool}:
  match o:
    case Tr.Put{+k, +p, +v}:
      tc.set_mpok(m, hs, Tr.Ent{k, p, v}, mk)
    case Tr.Del{+x}:
      tc.del_mpok(m, x, mk)

def tc.patch_mpok(ops: List<&2, Tr.Op>, +hs: List<&2, Nat>, +m: Tr.KMap, +mk: {LALogic.tc.mpok(m) == True{} : Bool}) -> {LALogic.tc.mpok(Tr.KMap.patch(ops, hs, m)) == True{} : Bool}:
  match ops:
    case Nil{}:
      mk
    case +o <> rest:
      tc.patch_mpok(rest, hs, Tr.KMap.exact(m, hs, o), tc.exact_mpok(m, hs, o, mk))

def tc.live_bst(+hs: List<&2, Nat>, +rs: List<&2, Tr.Rec>) -> {LLogicBool.tc.bst(Tr.KMap.go(rs, hs, Tr.KNil{})) == True{} : Bool}:
  LTree.tc.go_bst(rs, hs, Tr.KNil{}, {==})
