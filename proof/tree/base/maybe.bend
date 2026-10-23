# eukhe: lemmas the proofs of area tree share: maybe

import Base
import ../../../bend/tree.bend as Tr

def pt.MD(m: Maybe<&2, Tr.Ent>, n: Type, s: Type) -> Type:
  match m:
    case None{}:
      n
    case Some{x}:
      s

def pt.has_cons_go(b: Bool, +h: Tr.Ent, +r: List<&2, Tr.Ent>, +y: Nat) -> {Maybe.is_some(&2, Tr.Ent, Tr.get.go(h <> r, y, b)) == Bool.or(b, Tr.has(r, y)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# Rewind: reaches
# ---------------
# A lookup after a patch follows the ops on its key (`pt.look`); the dels
# drop exactly the keys b lacks, the puts set exactly the nodes a lacks or
# holds differently. So the patched tree and b agree on every key, and two
# sorted trees that agree on their keys are equal (`pt.ext`).

def tree.pt.pick(c: Bool, n: Maybe<&2, Tr.Ent>, m: Maybe<&2, Tr.Ent>) -> Maybe<&2, Tr.Ent>:
  match c:
    case True{}:
      n
    case False{}:
      m

# the node at key x after one op, from m
def pt.upd(o: Tr.Op, m: Maybe<&2, Tr.Ent>, +x: Nat) -> Maybe<&2, Tr.Ent>:
  match o:
    case Tr.Put{+k, p, v}:
      tree.pt.pick(Nat.is_eq(k, x), Some{Tr.Ent{k, p, v}}, m)
    case Tr.Del{k}:
      tree.pt.pick(Nat.is_eq(k, x), None{}, m)

# the node at key x after the ops, from m
def pt.look(ops: List<&2, Tr.Op>, m: Maybe<&2, Tr.Ent>, +x: Nat) -> Maybe<&2, Tr.Ent>:
  match ops:
    case Nil{}:
      m
    case o <> rest:
      pt.look(rest, pt.upd(o, m, x), x)

def pt.look_app(xs: List<&2, Tr.Op>, +ys: List<&2, Tr.Op>, +m: Maybe<&2, Tr.Ent>, +x: Nat) -> {pt.look(List.append(&2, Tr.Op, xs, ys), m, x) == pt.look(ys, pt.look(xs, m, x), x) : Maybe<&2, Tr.Ent>}:
  match xs:
    case Nil{}:
      {==}
    case +o <> +r:
      pt.look_app(r, ys, pt.upd(o, m, x), x)

def pt.pick_same(c: Bool, +m: Maybe<&2, Tr.Ent>) -> {tree.pt.pick(c, m, m) == m : Maybe<&2, Tr.Ent>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}
