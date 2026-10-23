# eukhe: lemmas the proofs of area tree share: tree/above

import Base
import ../../../../bend/tree.bend as Tr
import ../../../base/bool/and.bend as LBoolAnd
import ../../../base/bool/misc.bend as LBoolMisc
import ../../../base/nat/is_eq.bend as LNatIsEq
import ../../../base/nat/is_lt.bend as LNatIsLt
import ../bool.bend as LABool
import ../list.bend as LAList
import ../nat.bend as LANat
import ./Ent.bend as LATreeEnt

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
      LANat.pt.lt_trans(l, Tr.Ent.k(h), Tr.Ent.k(h2), al, LBoolAnd.tree.pt.and_l(Nat.is_lt(Tr.Ent.k(h), Tr.Ent.k(h2)), Tr.sorted(h2 <> r2), st))

def pt.above_unset_go(t: List<&2, Tr.Ent>, +x: Nat, hit: Bool, +l: Nat, al: {Tr.above(l, t) == True{} : Bool}, +st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.above(l, Tr.unset.go(t, x, hit)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match hit:
        case True{}:
          pt.above_unset_go(r, x, Tr.key.at(r, x), l, pt.above_tail(l, h, r, al, st), LBoolAnd.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st))
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
          pt.above_prune_go(r, g2, Tr.gone.at(r, g2), l, pt.above_tail(l, h, r, al, st), LBoolAnd.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st))
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

def tc.above_app(+k: Nat, r: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +ar: {Tr.above(k, r) == True{} : Bool}, +lk: {Nat.is_lt(k, b) == True{} : Bool}, +gb: {LBoolMisc.tc.ge(B, b) == True{} : Bool}) -> {Tr.above(k, List.append(&2, Tr.Ent, r, B)) == True{} : Bool}:
  match r:
    case Nil{}:
      match B:
        case Nil{}:
          {==}
        case +f <> s:
          LNatIsLt.tc.lt_le(k, b, Tr.Ent.k(f), lk, LNatIsLt.tc.ge_head(f, s, b, gb))
    case f <> s:
      ar

def tc.drops_gt(r: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool, +k: Nat, +ar: {Tr.above(k, r) == True{} : Bool}, +sr: {Tr.sorted(r) == True{} : Bool}) -> {LABool.tc.gtall(LAList.tc.dgo(r, gone, hit), k) == True{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case +f <> +r2:
      match hit:
        case True{}:
          +af = LBoolAnd.tree.pt.and_l(Tr.above(Tr.Ent.k(f), r2), Tr.sorted(r2), sr)
          +sr2 = LBoolAnd.tree.pt.and_r(Tr.above(Tr.Ent.k(f), r2), Tr.sorted(r2), sr)
          +ar2 = pt.above_lt(k, Tr.Ent.k(f), r2, ar, af)
          +g2 = {Tr.Ent.k(f) <> gone : List<&2, Nat>}
          LBoolAnd.tree.pt.and_t(Nat.is_lt(k, Tr.Ent.k(f)), LABool.tc.gtall(LAList.tc.dgo(r2, g2, Tr.gone.at(r2, g2)), k), ar, tc.drops_gt(r2, g2, Tr.gone.at(r2, g2), k, ar2, sr2))
        case False{}:
          +af = LBoolAnd.tree.pt.and_l(Tr.above(Tr.Ent.k(f), r2), Tr.sorted(r2), sr)
          +sr2 = LBoolAnd.tree.pt.and_r(Tr.above(Tr.Ent.k(f), r2), Tr.sorted(r2), sr)
          +ar2 = pt.above_lt(k, Tr.Ent.k(f), r2, ar, af)
          tc.drops_gt(r2, gone, Tr.gone.at(r2, gone), k, ar2, sr2)

# an unset of a key below every key of r keeps r
def tc.unset_above(r: List<&2, Tr.Ent>, +k: Nat, +ar: {Tr.above(k, r) == True{} : Bool}, +sr: {Tr.sorted(r) == True{} : Bool}) -> {Tr.unset(r, k) == r : List<&2, Tr.Ent>}:
  match r:
    case Nil{}:
      {==}
    case +f <> +r2:
      +ne = LNatIsEq.pt.lt_ne_r(k, Tr.Ent.k(f), ar)
      +af = LBoolAnd.tree.pt.and_l(Tr.above(Tr.Ent.k(f), r2), Tr.sorted(r2), sr)
      +sr2 = LBoolAnd.tree.pt.and_r(Tr.above(Tr.Ent.k(f), r2), Tr.sorted(r2), sr)
      %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(f), k), False{}, ne) : {Tr.unset.go(f <> r2, k, _) == f <> r2 : List<&2, Tr.Ent>}
      Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, ys => f <> ys, Tr.unset(r2, k), r2, tc.unset_above(r2, k, pt.above_lt(k, Tr.Ent.k(f), r2, ar, af), sr2))

# unsetting the keys a walk drops is the walk's prune
def tc.unsets_drops(t: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool, +st: {Tr.sorted(t) == True{} : Bool}) -> {LAList.tc.unsets(LAList.tc.dgo(t, gone, hit), t) == Tr.prune.go(t, gone, hit) : List<&2, Tr.Ent>}:
  match t:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +ar = LBoolAnd.tree.pt.and_l(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st)
          +sr = LBoolAnd.tree.pt.and_r(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st)
          +g2 = {Tr.Ent.k(e) <> gone : List<&2, Nat>}
          +D = LAList.tc.dgo(r, g2, Tr.gone.at(r, g2))
          %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(e), Tr.Ent.k(e)), True{}, Equal.sym(Bool, True{}, Nat.is_eq(Tr.Ent.k(e), Tr.Ent.k(e)), LANat.pt.eq_refl(Tr.Ent.k(e)))) : {LAList.tc.unsets(D, Tr.unset.go(e <> r, Tr.Ent.k(e), _)) == Tr.prune.go(r, g2, Tr.gone.at(r, g2)) : List<&2, Tr.Ent>}
          %Equal.sym(List<&2, Tr.Ent>, Tr.unset(r, Tr.Ent.k(e)), r, tc.unset_above(r, Tr.Ent.k(e), ar, sr)) : {LAList.tc.unsets(D, _) == Tr.prune.go(r, g2, Tr.gone.at(r, g2)) : List<&2, Tr.Ent>}
          tc.unsets_drops(r, g2, Tr.gone.at(r, g2), sr)
        case False{}:
          +ar = LBoolAnd.tree.pt.and_l(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st)
          +sr = LBoolAnd.tree.pt.and_r(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st)
          +D = LAList.tc.dgo(r, gone, Tr.gone.at(r, gone))
          +gt = tc.drops_gt(r, gone, Tr.gone.at(r, gone), Tr.Ent.k(e), ar, sr)
          Equal.trans(List<&2, Tr.Ent>, LAList.tc.unsets(D, e <> r), e <> LAList.tc.unsets(D, r), e <> Tr.prune.go(r, gone, Tr.gone.at(r, gone)), LATreeEnt.tc.unsets_cons(D, e, r, gt), Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, ys => e <> ys, LAList.tc.unsets(D, r), Tr.prune.go(r, gone, Tr.gone.at(r, gone)), tc.unsets_drops(r, gone, Tr.gone.at(r, gone), sr)))

def pd.above_app(+e: Tr.Ent, r: List<&2, Tr.Ent>, +x: Tr.Ent, +C: List<&2, Tr.Ent>, sa: {Tr.sorted(e <> r) == True{} : Bool}, la: {LABool.pd.lt_all(e <> r, Tr.Ent.k(x)) == True{} : Bool}) -> {Tr.above(Tr.Ent.k(e), List.append(&2, Tr.Ent, r, x <> C)) == True{} : Bool}:
  match r:
    case Nil{}:
      LBoolAnd.tree.pt.and_l(Nat.is_lt(Tr.Ent.k(e), Tr.Ent.k(x)), True{}, la)
    case +h <> +t:
      LBoolAnd.tree.pt.and_l(Tr.above(Tr.Ent.k(e), h <> t), Tr.sorted(h <> t), sa)
