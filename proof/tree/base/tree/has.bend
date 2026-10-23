# eukhe: lemmas the proofs of area tree share: tree/has

import Base
import ../../../../bend/tree.bend as Tr
import ../../../base/bool.bend as LBool
import ../../../base/logic/bool.bend as LLogicBool
import ../../../base/logic/logic.bend as LLogicLogic
import ../../../base/nat.bend as LNat
import ../../../base/tree.bend as LTree
import ../bool.bend as LABool
import ../logic.bend as LALogic
import ../maybe.bend as LAMaybe
import ./KMap.bend as LATreeKMap
import ./above.bend as LATreeAbove
import ./get.bend as LATreeGet

def pt.has_cons(+h: Tr.Ent, +r: List<&2, Tr.Ent>, +y: Nat) -> {Tr.has(h <> r, y) == Bool.or(Nat.is_eq(Tr.Ent.k(h), y), Tr.has(r, y)) : Bool}:
  LAMaybe.pt.has_cons_go(Nat.is_eq(Tr.Ent.k(h), y), h, r, y)

def pt.has_miss(+h: Tr.Ent, +r: List<&2, Tr.Ent>, +y: Nat, ne: {Nat.is_eq(Tr.Ent.k(h), y) == False{} : Bool}) -> {Tr.has(h <> r, y) == Tr.has(r, y) : Bool}:
  Equal.cong(Maybe<&2, Tr.Ent>, Bool, m => Maybe.is_some(&2, Tr.Ent, m), Tr.get(h <> r, y), Tr.get(r, y), LATreeGet.pt.get_miss(h, r, y, ne))

def pt.has_head(+h: Tr.Ent, +r: List<&2, Tr.Ent>) -> {Tr.has(h <> r, Tr.Ent.k(h)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(h <> r, Tr.Ent.k(h)), Some{h}, LATreeGet.pt.get_head(h, r)) : {Maybe.is_some(&2, Tr.Ent, _) == True{} : Bool}
  {==}

def pt.has_app(A: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, +y: Nat) -> {Tr.has(List.append(&2, Tr.Ent, A, C), y) == Bool.or(Tr.has(A, y), Tr.has(C, y)) : Bool}:
  match A:
    case Nil{}:
      {==}
    case +a <> +r:
      +ea = Nat.is_eq(Tr.Ent.k(a), y)
      +rc = List.append(&2, Tr.Ent, r, C)
      %Equal.sym(Bool, Tr.has(a <> rc, y), Bool.or(ea, Tr.has(rc, y)), pt.has_cons(a, rc, y)) : {_ == Bool.or(Tr.has(a <> r, y), Tr.has(C, y)) : Bool}
      %Equal.sym(Bool, Tr.has(rc, y), Bool.or(Tr.has(r, y), Tr.has(C, y)), pt.has_app(r, C, y)) : {Bool.or(ea, _) == Bool.or(Tr.has(a <> r, y), Tr.has(C, y)) : Bool}
      %Equal.sym(Bool, Tr.has(a <> r, y), Bool.or(ea, Tr.has(r, y)), pt.has_cons(a, r, y)) : {Bool.or(ea, Bool.or(Tr.has(r, y), Tr.has(C, y))) == Bool.or(_, Tr.has(C, y)) : Bool}
      Equal.sym(Bool, Bool.or(Bool.or(ea, Tr.has(r, y)), Tr.has(C, y)), Bool.or(ea, Bool.or(Tr.has(r, y), Tr.has(C, y))), LABool.pt.or_assoc(ea, Tr.has(r, y), Tr.has(C, y)))

def pt.has_app_l(+A: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, +y: Nat, h: {Tr.has(A, y) == True{} : Bool}) -> {Tr.has(List.append(&2, Tr.Ent, A, C), y) == True{} : Bool}:
  %Equal.sym(Bool, Tr.has(List.append(&2, Tr.Ent, A, C), y), Bool.or(Tr.has(A, y), Tr.has(C, y)), pt.has_app(A, C, y)) : {_ == True{} : Bool}
  LABool.pt.or_tl(Tr.has(A, y), Tr.has(C, y), h)

def pt.has_app_r(+A: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, +y: Nat, h: {Tr.has(C, y) == True{} : Bool}) -> {Tr.has(List.append(&2, Tr.Ent, A, C), y) == True{} : Bool}:
  %Equal.sym(Bool, Tr.has(List.append(&2, Tr.Ent, A, C), y), Bool.or(Tr.has(A, y), Tr.has(C, y)), pt.has_app(A, C, y)) : {_ == True{} : Bool}
  LABool.pt.or_tr(Tr.has(A, y), Tr.has(C, y), h)

# no node of a sorted list is below its first key
def pt.has_below(X: List<&2, Tr.Ent>, +y: Nat, +al: {Tr.above(y, X) == True{} : Bool}, +st: {Tr.sorted(X) == True{} : Bool}) -> {Tr.has(X, y) == False{} : Bool}:
  match X:
    case Nil{}:
      {==}
    case +h <> +r:
      Equal.trans(Bool, Tr.has(h <> r, y), Tr.has(r, y), False{}, pt.has_miss(h, r, y, LNat.pt.lt_ne_r(y, Tr.Ent.k(h), al)), pt.has_below(r, y, LATreeAbove.pt.above_tail(y, h, r, al, st), LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st)))

# A put
# -----

def pt.has_set_go(+t: List<&2, Tr.Ent>, +e: Tr.Ent, +y: Nat, b: Bool, eb: {Nat.is_eq(Tr.Ent.k(e), y) == b : Bool}, h: {Tr.has(t, y) == True{} : Bool}) -> {Tr.has(Tr.set(t, e), y) == True{} : Bool}:
  match b:
    case True{}:
      %LALogic.pt.eq_true(Tr.Ent.k(e), y, eb) : {Tr.has(Tr.set(t, e), _) == True{} : Bool}
      %Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(Tr.set(t, e), Tr.Ent.k(e)), Some{e}, LATreeGet.pt.get_set_same(t, e)) : {Maybe.is_some(&2, Tr.Ent, _) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(Tr.set(t, e), y), Tr.get(t, y), LATreeGet.pt.get_set_other(t, e, y, eb)) : {Maybe.is_some(&2, Tr.Ent, _) == True{} : Bool}
      h

# a set keeps every node there
def pt.has_set(+t: List<&2, Tr.Ent>, +e: Tr.Ent, +y: Nat, h: {Tr.has(t, y) == True{} : Bool}) -> {Tr.has(Tr.set(t, e), y) == True{} : Bool}:
  pt.has_set_go(t, e, y, Nat.is_eq(Tr.Ent.k(e), y), {==}, h)

def pt.or_has_set(b: Bool, +t: List<&2, Tr.Ent>, +e: Tr.Ent, +p: Nat, o: {Bool.or(b, Tr.has(t, p)) == True{} : Bool}) -> {Bool.or(b, Tr.has(Tr.set(t, e), p)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      pt.has_set(t, e, p, o)

def pt.or_mono_app(+b: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, +g: List<&2, Nat>, +x: Nat, c: Bool, ec: {Tr.has(b, x) == c : Bool}, h: {Bool.or(c, Tr.elem(g, x)) == True{} : Bool}) -> {Bool.or(Tr.has(List.append(&2, Tr.Ent, b, C), x), Tr.elem(g, x)) == True{} : Bool}:
  match c:
    case True{}:
      LABool.pt.or_tl(Tr.has(List.append(&2, Tr.Ent, b, C), x), Tr.elem(g, x), pt.has_app_l(b, C, x, ec))
    case False{}:
      LABool.pt.or_tr(Tr.has(List.append(&2, Tr.Ent, b, C), x), Tr.elem(g, x), h)

def pt.cov_b(A: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, +g: List<&2, Nat>, +ca: {LALogic.pt.cov(A, b, g) == True{} : Bool}) -> {LALogic.pt.cov(A, List.append(&2, Tr.Ent, b, C), g) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case +a <> +r:
      +i = Bool.or(Tr.has(b, Tr.Ent.k(a)), Tr.elem(g, Tr.Ent.k(a)))
      LBool.tree.pt.and_t(Bool.or(Tr.has(List.append(&2, Tr.Ent, b, C), Tr.Ent.k(a)), Tr.elem(g, Tr.Ent.k(a))), LALogic.pt.cov(r, List.append(&2, Tr.Ent, b, C), g), pt.or_mono_app(b, C, g, Tr.Ent.k(a), Tr.has(b, Tr.Ent.k(a)), {==}, LLogicBool.tree.pt.and_l(i, LALogic.pt.cov(r, b, g), ca)), pt.cov_b(r, b, C, g, LLogicBool.tree.pt.and_r(i, LALogic.pt.cov(r, b, g), ca)))

def pt.cov_has_go(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +g: List<&2, Nat>, +y: Nat, c: Bool, ec: {Nat.is_eq(Tr.Ent.k(e), y) == c : Bool}, he: {Bool.or(Tr.has(b, Tr.Ent.k(e)), Tr.elem(g, Tr.Ent.k(e))) == True{} : Bool}, ih: {Tr.has(r, y) == True{} : Bool} -> {Bool.or(Tr.has(b, y), Tr.elem(g, y)) == True{} : Bool}, hp: {Tr.has(e <> r, y) == True{} : Bool}) -> {Bool.or(Tr.has(b, y), Tr.elem(g, y)) == True{} : Bool}:
  match c:
    case True{}:
      %LALogic.pt.eq_true(Tr.Ent.k(e), y, ec) : {Bool.or(Tr.has(b, _), Tr.elem(g, _)) == True{} : Bool}
      he
    case False{}:
      ih(Equal.trans(Bool, Tr.has(r, y), Tr.has(e <> r, y), True{}, Equal.sym(Bool, Tr.has(e <> r, y), Tr.has(r, y), pt.has_miss(e, r, y, ec)), hp))

# a node of pre is kept or gone
def pt.cov_has(pre: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +g: List<&2, Nat>, +y: Nat, +cv: {LALogic.pt.cov(pre, b, g) == True{} : Bool}) -> {Tr.has(pre, y) == True{} : Bool} -> {Bool.or(Tr.has(b, y), Tr.elem(g, y)) == True{} : Bool}:
  match pre:
    case Nil{}:
      hp => LLogicLogic.tree.pt.absurdF({Bool.or(Tr.has(b, y), Tr.elem(g, y)) == True{} : Bool}, hp)
    case +e <> +r:
      +i = Bool.or(Tr.has(b, Tr.Ent.k(e)), Tr.elem(g, Tr.Ent.k(e)))
      +he = LLogicBool.tree.pt.and_l(i, LALogic.pt.cov(r, b, g), cv)
      ih = pt.cov_has(r, b, g, y, LLogicBool.tree.pt.and_r(i, LALogic.pt.cov(r, b, g), cv))
      hp => pt.cov_has_go(e, r, b, g, y, Nat.is_eq(Tr.Ent.k(e), y), {==}, he, ih, hp)

def pt.ok_keep_go(c: Bool, +pre: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +gone: List<&2, Nat>, +X: List<&2, Tr.Ent>, +p: Nat, o: {Bool.or(c, Tr.has(pre, p)) == True{} : Bool}, +cv: {LALogic.pt.cov(pre, b, gone) == True{} : Bool}, ng: {Tr.elem(gone, p) == False{} : Bool}) -> {Bool.or(c, Tr.has(List.append(&2, Tr.Ent, b, X), p)) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      +q = pt.cov_has(pre, b, gone, p, cv)(o)
      pt.has_app_l(b, X, p, LALogic.pt.or_l_true(Tr.has(b, p), Tr.elem(gone, p), q, ng))

def pt.allhas_cons(s: List<&2, Tr.Ent>, +h: Tr.Ent, +r: List<&2, Tr.Ent>, +ah: {LALogic.pt.allhas(s, r) == True{} : Bool}) -> {LALogic.pt.allhas(s, h <> r) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +rest:
      +i = Tr.has(r, Tr.Ent.k(e))
      +hd = Equal.trans(Bool, Tr.has(h <> r, Tr.Ent.k(e)), Bool.or(Nat.is_eq(Tr.Ent.k(h), Tr.Ent.k(e)), i), True{}, pt.has_cons(h, r, Tr.Ent.k(e)), LABool.pt.or_tr(Nat.is_eq(Tr.Ent.k(h), Tr.Ent.k(e)), i, LLogicBool.tree.pt.and_l(i, LALogic.pt.allhas(rest, r), ah)))
      LBool.tree.pt.and_t(Tr.has(h <> r, Tr.Ent.k(e)), LALogic.pt.allhas(rest, h <> r), hd, pt.allhas_cons(rest, h, r, LLogicBool.tree.pt.and_r(i, LALogic.pt.allhas(rest, r), ah)))

def pt.allhas_self(t: List<&2, Tr.Ent>) -> {LALogic.pt.allhas(t, t) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      LBool.tree.pt.and_t(Tr.has(h <> r, Tr.Ent.k(h)), LALogic.pt.allhas(r, h <> r), pt.has_head(h, r), pt.allhas_cons(r, h, r, pt.allhas_self(r)))

def tc.has_set.go(+t: List<&2, Tr.Ent>, +e: Tr.Ent, +y: Nat, b: Bool, eb: {Nat.is_eq(Tr.Ent.k(e), y) == b : Bool}) -> {Tr.has(Tr.set(t, e), y) == Bool.or(b, Tr.has(t, y)) : Bool}:
  match b:
    case True{}:
      %LALogic.pt.eq_true(Tr.Ent.k(e), y, eb) : {Tr.has(Tr.set(t, e), _) == True{} : Bool}
      Equal.cong(Maybe<&2, Tr.Ent>, Bool, z => Maybe.is_some(&2, Tr.Ent, z), Tr.get(Tr.set(t, e), Tr.Ent.k(e)), Some{e}, LATreeGet.pt.get_set_same(t, e))
    case False{}:
      Equal.cong(Maybe<&2, Tr.Ent>, Bool, z => Maybe.is_some(&2, Tr.Ent, z), Tr.get(Tr.set(t, e), y), Tr.get(t, y), LATreeGet.pt.get_set_other(t, e, y, eb))

# a set holds its key and every key it held
def tc.has_set(+t: List<&2, Tr.Ent>, +e: Tr.Ent, +y: Nat) -> {Tr.has(Tr.set(t, e), y) == Bool.or(Nat.is_eq(Tr.Ent.k(e), y), Tr.has(t, y)) : Bool}:
  tc.has_set.go(t, e, y, Nat.is_eq(Tr.Ent.k(e), y), {==})

# the gone keys hold exactly the keys of the gone list
def tc.bld_has(gone: List<&2, Nat>, +y: Nat) -> {Tr.has(LALogic.tc.bld(gone), y) == Tr.elem(gone, y) : Bool}:
  match gone:
    case Nil{}:
      {==}
    case +k <> +rest:
      Equal.trans(Bool, Tr.has(Tr.set(LALogic.tc.bld(rest), Tr.Ent{k, 0n, 0n}), y), Bool.or(Nat.is_eq(k, y), Tr.has(LALogic.tc.bld(rest), y)), Bool.or(Nat.is_eq(k, y), Tr.elem(rest, y)), tc.has_set(LALogic.tc.bld(rest), Tr.Ent{k, 0n, 0n}, y), Equal.cong(Bool, Bool, z => Bool.or(Nat.is_eq(k, y), z), Tr.has(LALogic.tc.bld(rest), y), Tr.elem(rest, y), tc.bld_has(rest, y)))

# the gone map holds what the gone list holds
def tc.ghas(+g: Tr.KMap, +gone: List<&2, Nat>, +y: Nat, +bt: {LLogicBool.tc.bst(g) == True{} : Bool}, +rg: {Tr.KMap.read(g) == LALogic.tc.bld(gone) : List<&2, Tr.Ent>}) -> {Tr.KMap.has(g, y) == Tr.elem(gone, y) : Bool}:
  Equal.trans(Bool, Tr.KMap.has(g, y), Tr.has(Tr.KMap.read(g), y), Tr.elem(gone, y), LATreeGet.tc.has(g, y, bt), Equal.trans(Bool, Tr.has(Tr.KMap.read(g), y), Tr.has(LALogic.tc.bld(gone), y), Tr.elem(gone, y), Equal.cong(List<&2, Tr.Ent>, Bool, z => Tr.has(z, y), Tr.KMap.read(g), LALogic.tc.bld(gone), rg), tc.bld_has(gone, y)))

# the gone test of the map is the gone test of the list
def tc.gin(s: List<&2, Tr.Ent>, +g: Tr.KMap, +gone: List<&2, Nat>, +bt: {LLogicBool.tc.bst(g) == True{} : Bool}, +rg: {Tr.KMap.read(g) == LALogic.tc.bld(gone) : List<&2, Tr.Ent>}) -> {Tr.gone.in(s, g) == Tr.gone.at(s, gone) : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> r:
      %Equal.sym(Bool, Tr.KMap.has(g, Tr.Ent.k(e)), Tr.elem(gone, Tr.Ent.k(e)), tc.ghas(g, gone, Tr.Ent.k(e), bt, rg)) : {Bool.or(_, Tr.KMap.has(g, Tr.Ent.p(e))) == Bool.or(Tr.elem(gone, Tr.Ent.k(e)), Tr.elem(gone, Tr.Ent.p(e))) : Bool}
      %Equal.sym(Bool, Tr.KMap.has(g, Tr.Ent.p(e)), Tr.elem(gone, Tr.Ent.p(e)), tc.ghas(g, gone, Tr.Ent.p(e), bt, rg)) : {Bool.or(Tr.elem(gone, Tr.Ent.k(e)), _) == Bool.or(Tr.elem(gone, Tr.Ent.k(e)), Tr.elem(gone, Tr.Ent.p(e))) : Bool}
      {==}

# the walk over the gone map drops what the walk over the gone list drops
def tc.ds(s: List<&2, Tr.Ent>, +hs: List<&2, Nat>, +g: Tr.KMap, +gone: List<&2, Nat>, hit: Bool, +bt: {LLogicBool.tc.bst(g) == True{} : Bool}, +rg: {Tr.KMap.read(g) == LALogic.tc.bld(gone) : List<&2, Tr.Ent>}) -> {Tr.drops.s(s, hs, g, hit) == LALogic.tc.dgo(s, gone, hit) : List<&2, Nat>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +k = Tr.Ent.k(e)
          +g2 = Tr.gone.of(hs, g, k)
          +gn = {k <> gone : List<&2, Nat>}
          +bt2 = LTree.tc.set_bst(g, hs, Tr.Ent{k, 0n, 0n}, bt)
          +rg2 = LATreeKMap.tc.gone_of(hs, g, gone, k, bt, rg)
          %Equal.sym(Bool, Tr.gone.in(r, g2), Tr.gone.at(r, gn), tc.gin(r, g2, gn, bt2, rg2)) : {k <> Tr.drops.s(r, hs, g2, _) == k <> LALogic.tc.dgo(r, gn, Tr.gone.at(r, gn)) : List<&2, Nat>}
          Equal.cong(List<&2, Nat>, List<&2, Nat>, z => k <> z, Tr.drops.s(r, hs, g2, Tr.gone.at(r, gn)), LALogic.tc.dgo(r, gn, Tr.gone.at(r, gn)), tc.ds(r, hs, g2, gn, Tr.gone.at(r, gn), bt2, rg2))
        case False{}:
          %Equal.sym(Bool, Tr.gone.in(r, g), Tr.gone.at(r, gone), tc.gin(r, g, gone, bt, rg)) : {Tr.drops.s(r, hs, g, _) == LALogic.tc.dgo(r, gone, Tr.gone.at(r, gone)) : List<&2, Nat>}
          tc.ds(r, hs, g, gone, Tr.gone.at(r, gone), bt, rg)

# a delete's walk with the gone map drops what the walk with the gone list
# [x] drops
def tc.drops(+s: List<&2, Tr.Ent>, +hs: List<&2, Nat>, +x: Nat) -> {Tr.drops(s, hs, x) == LALogic.tc.dgo(s, [x], Tr.gone.at(s, [x])) : List<&2, Nat>}:
  +g = Tr.gone.of(hs, Tr.KNil{}, x)
  +bt = LTree.tc.set_bst(Tr.KNil{}, hs, Tr.Ent{x, 0n, 0n}, {==})
  +rg = LATreeKMap.tc.gone_of(hs, Tr.KNil{}, Nil{}, x, {==}, {==})
  %Equal.sym(Bool, Tr.gone.in(s, g), Tr.gone.at(s, [x]), tc.gin(s, g, [x], bt, rg)) : {Tr.drops.s(s, hs, g, _) == LALogic.tc.dgo(s, [x], Tr.gone.at(s, [x])) : List<&2, Nat>}
  tc.ds(s, hs, g, [x], Tr.gone.at(s, [x]), bt, rg)

# The stack in the tree: parents
# ------------------------------

def pd.or_has_app(c: Bool, +all: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, +p: Nat, o: {Bool.or(c, Tr.has(all, p)) == True{} : Bool}) -> {Bool.or(c, Tr.has(List.append(&2, Tr.Ent, all, C), p)) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      pt.has_app_l(all, C, p, o)
