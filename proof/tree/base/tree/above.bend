# eukhe: lemmas the proofs of area tree share: tree/above

import Base
import ../../../../bend/tree.bend as Tr
import ../../../base/bool.bend as LBool
import ../../../base/logic/bool.bend as LLogicBool
import ../../../base/nat.bend as LNat
import ../logic.bend as LALogic
import ../nat.bend as LANat

# Order
# -----

def pt.above_set_go(t: List<&2, Tr.Ent>, +e: Tr.Ent, c: Cmp, +l: Nat, al: {Tr.above(l, t) == True{} : Bool}, le: {Nat.is_lt(l, Tr.Ent.k(e)) == True{} : Bool}) -> {Tr.above(l, Tr.set.go(t, e, c)) == True{} : Bool}:
  match t:
    case Nil{}:
      le
    case +h <> +r:
      match c:
        case LT{}:
          le
        case EQ{}:
          le
        case GT{}:
          al

def pt.above_tail(+l: Nat, +h: Tr.Ent, r: List<&2, Tr.Ent>, al: {Tr.above(l, h <> r) == True{} : Bool}, st: {Tr.sorted(h <> r) == True{} : Bool}) -> {Tr.above(l, r) == True{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case +h2 <> +r2:
      LANat.pt.lt_trans(l, Tr.Ent.k(h), Tr.Ent.k(h2), al, LLogicBool.tree.pt.and_l(Nat.is_lt(Tr.Ent.k(h), Tr.Ent.k(h2)), Tr.sorted(h2 <> r2), st))

def pt.above_unset_go(t: List<&2, Tr.Ent>, +x: Nat, hit: Bool, +l: Nat, al: {Tr.above(l, t) == True{} : Bool}, +st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.above(l, Tr.unset.go(t, x, hit)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match hit:
        case True{}:
          pt.above_unset_go(r, x, Tr.key.at(r, x), l, pt.above_tail(l, h, r, al, st), LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st))
        case False{}:
          al

# A delete
# --------

def pt.above_prune_go(t: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool, +l: Nat, al: {Tr.above(l, t) == True{} : Bool}, +st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.above(l, Tr.prune.go(t, gone, hit)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match hit:
        case True{}:
          +g2 = {Tr.Ent.k(h) <> gone : List<&2, Nat>}
          pt.above_prune_go(r, g2, Tr.gone.at(r, g2), l, pt.above_tail(l, h, r, al, st), LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st))
        case False{}:
          al

def pt.or_above_tail(c: Bool, +g: Nat, +e: Tr.Ent, +r: List<&2, Tr.Ent>, h: {Bool.or(c, Tr.above(g, e <> r)) == True{} : Bool}, +st: {Tr.sorted(e <> r) == True{} : Bool}) -> {Bool.or(c, Tr.above(g, r)) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      pt.above_tail(g, e, r, h, st)

def pt.above_lt(+a: Nat, +b: Nat, r: List<&2, Tr.Ent>, ab: {Nat.is_lt(a, b) == True{} : Bool}, br: {Tr.above(b, r) == True{} : Bool}) -> {Tr.above(a, r) == True{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case +h <> +rest:
      LANat.pt.lt_trans(a, b, Tr.Ent.k(h), ab, br)

def tc.above_app(+k: Nat, r: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +ar: {Tr.above(k, r) == True{} : Bool}, +lk: {Nat.is_lt(k, b) == True{} : Bool}, +gb: {LLogicBool.tc.ge(B, b) == True{} : Bool}) -> {Tr.above(k, List.append(&2, Tr.Ent, r, B)) == True{} : Bool}:
  match r:
    case Nil{}:
      match B:
        case Nil{}:
          {==}
        case +f <> s:
          LNat.tc.lt_le(k, b, Tr.Ent.k(f), lk, LNat.tc.ge_head(f, s, b, gb))
    case f <> s:
      ar

def tc.drops_gt(r: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool, +k: Nat, +ar: {Tr.above(k, r) == True{} : Bool}, +sr: {Tr.sorted(r) == True{} : Bool}) -> {LALogic.tc.gtall(LALogic.tc.dgo(r, gone, hit), k) == True{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case +f <> +r2:
      match hit:
        case True{}:
          +af = LLogicBool.tree.pt.and_l(Tr.above(Tr.Ent.k(f), r2), Tr.sorted(r2), sr)
          +sr2 = LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(f), r2), Tr.sorted(r2), sr)
          +ar2 = pt.above_lt(k, Tr.Ent.k(f), r2, ar, af)
          +g2 = {Tr.Ent.k(f) <> gone : List<&2, Nat>}
          LBool.tree.pt.and_t(Nat.is_lt(k, Tr.Ent.k(f)), LALogic.tc.gtall(LALogic.tc.dgo(r2, g2, Tr.gone.at(r2, g2)), k), ar, tc.drops_gt(r2, g2, Tr.gone.at(r2, g2), k, ar2, sr2))
        case False{}:
          +af = LLogicBool.tree.pt.and_l(Tr.above(Tr.Ent.k(f), r2), Tr.sorted(r2), sr)
          +sr2 = LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(f), r2), Tr.sorted(r2), sr)
          +ar2 = pt.above_lt(k, Tr.Ent.k(f), r2, ar, af)
          tc.drops_gt(r2, gone, Tr.gone.at(r2, gone), k, ar2, sr2)

def pd.above_app(+e: Tr.Ent, r: List<&2, Tr.Ent>, +x: Tr.Ent, +C: List<&2, Tr.Ent>, sa: {Tr.sorted(e <> r) == True{} : Bool}, la: {LALogic.pd.lt_all(e <> r, Tr.Ent.k(x)) == True{} : Bool}) -> {Tr.above(Tr.Ent.k(e), List.append(&2, Tr.Ent, r, x <> C)) == True{} : Bool}:
  match r:
    case Nil{}:
      LLogicBool.tree.pt.and_l(Nat.is_lt(Tr.Ent.k(e), Tr.Ent.k(x)), True{}, la)
    case +h <> +t:
      LLogicBool.tree.pt.and_l(Tr.above(Tr.Ent.k(e), h <> t), Tr.sorted(h <> t), sa)

def tc.gb_tail(gone: List<&2, Nat>, +x: Nat, +e: Tr.Ent, +r: List<&2, Tr.Ent>, +g: {LALogic.tc.gb(gone, x, e <> r) == True{} : Bool}, +st: {Tr.sorted(e <> r) == True{} : Bool}) -> {LALogic.tc.gb(gone, x, r) == True{} : Bool}:
  match gone:
    case Nil{}:
      {==}
    case +z <> +rest:
      +hd = LLogicBool.tree.pt.and_l(Bool.or(Nat.is_eq(z, x), Tr.above(z, e <> r)), LALogic.tc.gb(rest, x, e <> r), g)
      +tl = LLogicBool.tree.pt.and_r(Bool.or(Nat.is_eq(z, x), Tr.above(z, e <> r)), LALogic.tc.gb(rest, x, e <> r), g)
      LBool.tree.pt.and_t(Bool.or(Nat.is_eq(z, x), Tr.above(z, r)), LALogic.tc.gb(rest, x, r), pt.or_above_tail(Nat.is_eq(z, x), z, e, r, hd, st), tc.gb_tail(rest, x, e, r, tl, st))
