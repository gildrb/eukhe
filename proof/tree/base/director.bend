# eukhe: lemmas the proofs of area tree share: director

import Base
import ../../../bend/director.bend as Dr
import ../../../bend/tree.bend as Tr
import ../../base/bool/and.bend as LBoolAnd
import ../../base/nat/is_lt.bend as LNatIsLt
import ./bool.bend as LABool
import ./list.bend as LAList
import ./nat.bend as LANat
import ./tree/rooted.bend as LATreeRooted
import ./tree/sorted.bend as LATreeSorted

# every key of encode(s) is at most twice the layers of s
def pd.enc_lt(s: List<&2, Dr.Layer>, +m: Nat, +h: {Nat.is_lt(Nat.double(List.length(&2, Dr.Layer, s)), m) == True{} : Bool}) -> {LABool.pd.lt_all(Dr.encode(s), m) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case l <> +rest:
      match l:
        case Dr.Layer{+k, +b}:
          +n = List.length(&2, Dr.Layer, rest)
          +x = {Tr.Ent{1n+Nat.double(n), Dr.kind.parent(n), k} : Tr.Ent}
          +y = {Tr.Ent{2n+Nat.double(n), 1n+Nat.double(n), b} : Tr.Ent}
          +hr = LANat.pt.lt_trans(Nat.double(n), 2n+Nat.double(n), m, LANat.pd.lt_add2(Nat.double(n)), h)
          +hx = LANat.pt.lt_trans(1n+Nat.double(n), 2n+Nat.double(n), m, LNatIsLt.pd.lt_succ(1n+Nat.double(n)), h)
          +hxy = LBoolAnd.tree.pt.and_t(Nat.is_lt(1n+Nat.double(n), m), Bool.and(Nat.is_lt(2n+Nat.double(n), m), True{}), hx, LBoolAnd.tree.pt.and_t(Nat.is_lt(2n+Nat.double(n), m), True{}, h, {==}))
          LAList.pd.lt_all_app(Dr.encode(rest), [x, y], m, pd.enc_lt(rest, m, hr), hxy)

def pd.enc_sorted(s: List<&2, Dr.Layer>) -> {Tr.sorted(Dr.encode(s)) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case l <> +rest:
      match l:
        case Dr.Layer{+k, +b}:
          +n = List.length(&2, Dr.Layer, rest)
          +x = {Tr.Ent{1n+Nat.double(n), Dr.kind.parent(n), k} : Tr.Ent}
          +y = {Tr.Ent{2n+Nat.double(n), 1n+Nat.double(n), b} : Tr.Ent}
          +sxy = LBoolAnd.tree.pt.and_t(Nat.is_lt(1n+Nat.double(n), 2n+Nat.double(n)), Tr.sorted([y]), LNatIsLt.pd.lt_succ(1n+Nat.double(n)), {==})
          LATreeSorted.pd.sorted_snoc(Dr.encode(rest), x, [y], pd.enc_sorted(rest), sxy, pd.enc_lt(rest, 1n+Nat.double(n), LNatIsLt.pd.lt_succ(Nat.double(n))))

def pd.dir_encode_sound(+s: List<&2, Dr.Layer>) -> {Tr.sound(Dr.encode(s)) == True{} : Bool}:
  LBoolAnd.tree.pt.and_t(Tr.sorted(Dr.encode(s)), Tr.rooted(Dr.encode(s)), pd.enc_sorted(s), LATreeRooted.pd.enc_rooted(s))
