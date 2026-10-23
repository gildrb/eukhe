# eukhe: lemmas the proofs of area tree share: bool

import Base
import ../../../bend/tree.bend as Tr
import ../../base/bool.bend as LBool
import ../../base/logic/bool.bend as LLogicBool
import ../../base/logic/logic.bend as LLogicLogic
import ./logic.bend as LALogic

def pt.or_tl(+a: Bool, +b: Bool, ha: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.or(_, b) == True{} : Bool}
  {==}

def pt.or_tr(a: Bool, +b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

def tree.pt.or_false_r(a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pt.or_assoc(a: Bool, +b: Bool, +c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pt.or_mono_elem(c: Bool, +g: List<&2, Nat>, +y: Nat, +x: Nat, h: {Bool.or(c, Tr.elem(g, x)) == True{} : Bool}) -> {Bool.or(c, Tr.elem(y <> g, x)) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      pt.or_tr(Nat.is_eq(y, x), Tr.elem(g, x), h)

def pt.cov_gone(A: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +g: List<&2, Nat>, +y: Nat, +ca: {LALogic.pt.cov(A, b, g) == True{} : Bool}) -> {LALogic.pt.cov(A, b, y <> g) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case +a <> +r:
      +i = Bool.or(Tr.has(b, Tr.Ent.k(a)), Tr.elem(g, Tr.Ent.k(a)))
      LBool.tree.pt.and_t(Bool.or(Tr.has(b, Tr.Ent.k(a)), Tr.elem(y <> g, Tr.Ent.k(a))), LALogic.pt.cov(r, b, y <> g), pt.or_mono_elem(Tr.has(b, Tr.Ent.k(a)), g, y, Tr.Ent.k(a), LLogicBool.tree.pt.and_l(i, LALogic.pt.cov(r, b, g), ca)), pt.cov_gone(r, b, g, y, LLogicBool.tree.pt.and_r(i, LALogic.pt.cov(r, b, g), ca)))

def tc.or_ff(a: Bool, b: Bool, ha: {a == False{} : Bool}, hb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  match a:
    case True{}:
      LLogicLogic.pt.absurd({Bool.or(True{}, b) == False{} : Bool}, ha)
    case False{}:
      hb

def tc.mpok_rest(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {LALogic.tc.mpok(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {Bool.and(LALogic.tc.mpok(r), Bool.and(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r)))) == True{} : Bool}:
  LLogicBool.tree.pt.and_r(LALogic.tc.mpok(l), Bool.and(LALogic.tc.mpok(r), Bool.and(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r)))), h)

def tc.mpok_r(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {LALogic.tc.mpok(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {LALogic.tc.mpok(r) == True{} : Bool}:
  LLogicBool.tree.pt.and_l(LALogic.tc.mpok(r), Bool.and(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r))), tc.mpok_rest(mid, mp, l, r, h))
