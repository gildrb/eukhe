# eukhe: lemmas of LAW tree_replay_spec: on a sorted tree the model's set
# is the spec's put (the node's key dropped, the node inserted in key
# order), and so a rewind's patch is the spec's.

import Base
import ../../../bend/tree.bend as Tr
import ../../../spec/durable/tree.bend as TS
import ../../base/logic/bool.bend as LLogicBool
import ../base/logic.bend as LALogic
import ../base/nat.bend as LANat
import ../base/tree/sorted.bend as LATreeSorted
import ../base/tree/unset.bend as LATreeUnset
import ./basic.bend as LB

def ts.CT(c: Cmp, l: Type, e: Type, g: Type) -> Type:
  match c:
    case LT{}:
      l
    case EQ{}:
      e
    case GT{}:
      g

def ts.eq_gt(-G: Type, e: {EQ{} == GT{} : Cmp}) -> G:
  %e : ts.CT(_, Unit, Unit, G)
  Unit{}

def ts.lt_gt(-G: Type, e: {LT{} == GT{} : Cmp}) -> G:
  %e : ts.CT(_, Unit, Unit, G)
  Unit{}

# a above b: b is not a
def ts.gt_ne(a: Nat, b: Nat, h: {Nat.cmp(a, b) == GT{} : Cmp}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      ts.eq_gt({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      ts.lt_gt({Nat.is_eq(1n+q, 0n) == False{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ts.gt_ne(p, q, h)

def ts.gt_nlt(+a: Nat, +b: Nat, h: {Nat.cmp(a, b) == GT{} : Cmp}) -> {Nat.is_lt(a, b) == False{} : Bool}:
  %Equal.sym(Cmp, Nat.cmp(a, b), GT{}, h) : {Cmp.is_lt(_) == False{} : Bool}
  {==}

# a node below the first key of r goes in front
def ts.ins_head(+e: Tr.Ent, r: List<&2, Tr.Ent>, h: {TS.first_above(TS.key(e), r) == True{} : Bool}) -> {TS.ins(r, e, TS.ins.first(e, r)) == e <> r : List<&2, Tr.Ent>}:
  match r:
    case Nil{}:
      {==}
    case +h2 <> +r2:
      %Equal.sym(Bool, TS.first_above(TS.key(e), h2 <> r2), True{}, h) : {TS.ins(h2 <> r2, e, _) == e <> h2 <> r2 : List<&2, Tr.Ent>}
      {==}

# no node of a sorted r is at a key below its first: the spec drops none
def ts.without_above(+r: List<&2, Tr.Ent>, +k: Nat, +ar: {Tr.above(k, r) == True{} : Bool}, +sr: {Tr.sorted(r) == True{} : Bool}) -> {TS.without(r, k) == r : List<&2, Tr.Ent>}:
  Equal.trans(List<&2, Tr.Ent>, TS.without(r, k), Tr.unset(r, k), r, Equal.sym(List<&2, Tr.Ent>, Tr.unset(r, k), TS.without(r, k), LB.ts.unset(r, k)), LATreeUnset.tc.unset_above(r, k, ar, sr))

def ts.above_rw(-a: Nat, -b: Nat, -r: List<&2, Tr.Ent>, e: {a == b : Nat}, h: {Tr.above(b, r) == True{} : Bool}) -> {Tr.above(a, r) == True{} : Bool}:
  %Equal.sym(Nat, a, b, e) : {Tr.above(_, r) == True{} : Bool}
  h

# a set at the key of the first node
def ts.set_eq(+k: Nat, +p: Nat, +v: Nat, +ph: Nat, +vh: Nat, +rest: List<&2, Tr.Ent>, +ar: {Tr.above(k, rest) == True{} : Bool}, +sr: {Tr.sorted(rest) == True{} : Bool}) -> {Tr.Ent{k, p, v} <> rest == TS.put(Tr.Ent{k, ph, vh} <> rest, Tr.Ent{k, p, v}) : List<&2, Tr.Ent>}:
  +E = {Tr.Ent{k, p, v} : Tr.Ent}
  %LANat.pt.eq_refl(k) : {E <> rest == TS.ins(TS.keep.if(Bool.not(_), Tr.Ent{k, ph, vh}, TS.without(rest, k)), E, TS.ins.first(E, TS.keep.if(Bool.not(_), Tr.Ent{k, ph, vh}, TS.without(rest, k)))) : List<&2, Tr.Ent>}
  %Equal.sym(List<&2, Tr.Ent>, TS.without(rest, k), rest, ts.without_above(rest, k, ar, sr)) : {E <> rest == TS.ins(_, E, TS.ins.first(E, _)) : List<&2, Tr.Ent>}
  +fa = Equal.trans(Bool, TS.first_above(k, rest), Tr.above(k, rest), True{}, Equal.sym(Bool, Tr.above(k, rest), TS.first_above(k, rest), LB.ts.above(k, rest)), ar)
  Equal.sym(List<&2, Tr.Ent>, TS.ins(rest, E, TS.ins.first(E, rest)), E <> rest, ts.ins_head(E, rest, fa))

def ts.set_at(c: Cmp, +k: Nat, +p: Nat, +v: Nat, +kh: Nat, +ph: Nat, +vh: Nat, +rest: List<&2, Tr.Ent>, +ec: {Nat.cmp(k, kh) == c : Cmp}, +st: {Tr.sorted(Tr.Ent{kh, ph, vh} <> rest) == True{} : Bool}, ih: {Tr.set(rest, Tr.Ent{k, p, v}) == TS.put(rest, Tr.Ent{k, p, v}) : List<&2, Tr.Ent>}) -> {Tr.set.go(Tr.Ent{kh, ph, vh} <> rest, Tr.Ent{k, p, v}, c) == TS.put(Tr.Ent{kh, ph, vh} <> rest, Tr.Ent{k, p, v}) : List<&2, Tr.Ent>}:
  match c:
    case LT{}:
      +E = {Tr.Ent{k, p, v} : Tr.Ent}
      +H = {Tr.Ent{kh, ph, vh} : Tr.Ent}
      +lt = LANat.pt.cmp_lt(k, kh, ec)
      %Equal.sym(List<&2, Tr.Ent>, TS.without(H <> rest, k), H <> rest, ts.without_above(H <> rest, k, lt, st)) : {E <> H <> rest == TS.ins(_, E, TS.ins.first(E, _)) : List<&2, Tr.Ent>}
      Equal.sym(List<&2, Tr.Ent>, TS.ins(H <> rest, E, TS.ins.first(E, H <> rest)), E <> H <> rest, ts.ins_head(E, H <> rest, lt))
    case EQ{}:
      +keq = LALogic.pt.cmp_eq(k, kh, ec)
      +ar = LLogicBool.tree.pt.and_l(Tr.above(kh, rest), Tr.sorted(rest), st)
      +sr = LLogicBool.tree.pt.and_r(Tr.above(kh, rest), Tr.sorted(rest), st)
      %keq : {Tr.Ent{k, p, v} <> rest == TS.put(Tr.Ent{_, ph, vh} <> rest, Tr.Ent{k, p, v}) : List<&2, Tr.Ent>}
      ts.set_eq(k, p, v, ph, vh, rest, ts.above_rw(k, kh, rest, keq, ar), sr)
    case GT{}:
      +E = {Tr.Ent{k, p, v} : Tr.Ent}
      +H = {Tr.Ent{kh, ph, vh} : Tr.Ent}
      %Equal.sym(Bool, Nat.is_eq(kh, k), False{}, ts.gt_ne(k, kh, ec)) : {H <> Tr.set(rest, E) == TS.ins(TS.keep.if(Bool.not(_), H, TS.without(rest, k)), E, TS.ins.first(E, TS.keep.if(Bool.not(_), H, TS.without(rest, k)))) : List<&2, Tr.Ent>}
      %Equal.sym(Bool, Nat.is_lt(k, kh), False{}, ts.gt_nlt(k, kh, ec)) : {H <> Tr.set(rest, E) == TS.ins(H <> TS.without(rest, k), E, _) : List<&2, Tr.Ent>}
      %Equal.sym(List<&2, Tr.Ent>, Tr.set(rest, E), TS.put(rest, E), ih) : {H <> _ == H <> TS.put(rest, E) : List<&2, Tr.Ent>}
      {==}

# on a sorted tree the model's set of node {k, p, v} is the spec's put
def ts.set(t: List<&2, Tr.Ent>, +k: Nat, +p: Nat, +v: Nat, +st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.set(t, Tr.Ent{k, p, v}) == TS.put(t, Tr.Ent{k, p, v}) : List<&2, Tr.Ent>}:
  match t:
    case Nil{}:
      {==}
    case +h <> +rest:
      match h:
        case Tr.Ent{+kh, +ph, +vh}:
          +sr = LLogicBool.tree.pt.and_r(Tr.above(kh, rest), Tr.sorted(rest), st)
          ts.set_at(Nat.cmp(k, kh), k, p, v, kh, ph, vh, rest, {==}, st, ts.set(rest, k, p, v, sr))

# one exact op on a sorted tree
def ts.exact(+t: List<&2, Tr.Ent>, o: Tr.Op, +st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.exact(t, o) == TS.exact(t, o) : List<&2, Tr.Ent>}:
  match o:
    case Tr.Put{+k, +p, +v}:
      ts.set(t, k, p, v, st)
    case Tr.Del{x}:
      LB.ts.unset(t, x)

# a rewind's ops on a sorted tree
def ts.patch(ops: List<&2, Tr.Op>, +t: List<&2, Tr.Ent>, +st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.patch(ops, t) == TS.patch(ops, t) : List<&2, Tr.Ent>}:
  match ops:
    case Nil{}:
      {==}
    case +o <> rest:
      %ts.exact(t, o, st) : {Tr.patch(rest, Tr.exact(t, o)) == TS.patch(rest, _) : List<&2, Tr.Ent>}
      ts.patch(rest, Tr.exact(t, o), LATreeSorted.pt.sorted_exact(t, o, st))
