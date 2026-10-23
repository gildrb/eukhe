# eukhe: lemmas the proofs of area tree share: tree/ok

import Base
import ../../../../bend/director.bend as Dr
import ../../../../bend/tree.bend as Tr
import ../../../base/bool.bend as LBool
import ../../../base/logic/bool.bend as LLogicBool
import ../bool.bend as LABool
import ../logic.bend as LALogic
import ../nat.bend as LANat
import ./has.bend as LATreeHas

def pt.ok_set(+t: List<&2, Tr.Ent>, +e: Tr.Ent, +k: Nat, +p: Nat, +h: {Tr.ok(t, k, p) == True{} : Bool}) -> {Tr.ok(Tr.set(t, e), k, p) == True{} : Bool}:
  +o = LLogicBool.tree.pt.and_r(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(t, p)), h)
  LBool.tree.pt.and_t(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(Tr.set(t, e), p)), LLogicBool.tree.pt.and_l(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(t, p)), h), LATreeHas.pt.or_has_set(Nat.is_eq(p, 0n), t, e, p, o))

# a kept node still hangs under the root or a kept node
def pt.ok_keep(+pre: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +gone: List<&2, Nat>, +X: List<&2, Tr.Ent>, +k: Nat, +p: Nat, +op: {Tr.ok(pre, k, p) == True{} : Bool}, +cv: {LALogic.pt.cov(pre, b, gone) == True{} : Bool}, ng: {Tr.elem(gone, p) == False{} : Bool}) -> {Tr.ok(List.append(&2, Tr.Ent, b, X), k, p) == True{} : Bool}:
  +o = LLogicBool.tree.pt.and_r(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(pre, p)), op)
  LBool.tree.pt.and_t(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(List.append(&2, Tr.Ent, b, X), p)), LLogicBool.tree.pt.and_l(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(pre, p)), op), LATreeHas.pt.ok_keep_go(Nat.is_eq(p, 0n), pre, b, gone, X, p, o, cv, ng))

# a parent stays a parent when nodes come after
def pd.ok_app(+all: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, +k: Nat, +p: Nat, +h: {Tr.ok(all, k, p) == True{} : Bool}) -> {Tr.ok(List.append(&2, Tr.Ent, all, C), k, p) == True{} : Bool}:
  +o = LLogicBool.tree.pt.and_r(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(all, p)), h)
  LBool.tree.pt.and_t(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(List.append(&2, Tr.Ent, all, C), p)), LLogicBool.tree.pt.and_l(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(all, p)), h), LATreeHas.pd.or_has_app(Nat.is_eq(p, 0n), all, C, p, o))

# the kind node of the layer above rest hangs under the root (no layer
# below) or the kind node of the layer below
def pd.parent_ok(rest: List<&2, Dr.Layer>, +C: List<&2, Tr.Ent>) -> {Tr.ok(List.append(&2, Tr.Ent, Dr.encode(rest), C), Dr.kind.key(List.length(&2, Dr.Layer, rest)), Dr.kind.parent(List.length(&2, Dr.Layer, rest))) == True{} : Bool}:
  match rest:
    case Nil{}:
      {==}
    case l2 <> +r2:
      match l2:
        case Dr.Layer{+k2, +b2}:
          +m = List.length(&2, Dr.Layer, r2)
          +E2 = Dr.encode(r2)
          +x2 = {Tr.Ent{1n+Nat.double(m), Dr.kind.parent(m), k2} : Tr.Ent}
          +y2 = {Tr.Ent{2n+Nat.double(m), 1n+Nat.double(m), b2} : Tr.Ent}
          +X2 = {[x2, y2] : List<&2, Tr.Ent>}
          +hh = LATreeHas.pt.has_app_l(List.append(&2, Tr.Ent, E2, X2), C, 1n+Nat.double(m), LATreeHas.pt.has_app_r(E2, X2, 1n+Nat.double(m), LATreeHas.pt.has_head(x2, [y2])))
          LBool.tree.pt.and_t(Nat.is_lt(1n+Nat.double(m), 3n+Nat.double(m)), Bool.or(Nat.is_eq(1n+Nat.double(m), 0n), Tr.has(List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, E2, X2), C), 1n+Nat.double(m))), LANat.pd.lt_add2(1n+Nat.double(m)), LABool.pt.or_tr(Nat.is_eq(1n+Nat.double(m), 0n), Tr.has(List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, E2, X2), C), 1n+Nat.double(m)), hh))
