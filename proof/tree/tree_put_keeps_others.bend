# eukhe: the proof of LAW tree_put_keeps_others

import Base
import ../../bend/tree.bend as Tr
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

def pt.put_at_other(+t: List<&2, Tr.Ent>, +k: Nat, +p: Nat, +v: Nat, +x: Nat, b: Bool, ne: {Nat.is_eq(k, x) == False{} : Bool}) -> {Tr.get(Tr.put.at(b, t, Tr.Ent{k, p, v}), x) == Tr.get(t, x) : Maybe<&2, Tr.Ent>}:
  match b:
    case True{}:
      LA.pt.get_set_other(t, Tr.Ent{k, p, v}, x, ne)
    case False{}:
      {==}

def put_keeps_others(+t: List<&2, Tr.Ent>, good: {Tr.sound(t) == True{} : Bool}, +k: Nat, +p: Nat, +v: Nat, +x: Nat, other: {Nat.is_eq(x, k) == False{} : Bool}) -> {Tr.get(Tr.apply(t, Tr.Do{Tr.Put{k, p, v}}), x) == Tr.get(t, x) : Maybe<&2, Tr.Ent>}:
  pt.put_at_other(t, k, p, v, x, Tr.ok(t, k, p), L.pt.ne_comm(x, k, other))

def Laws.tree_put_keeps_others(t, L.good, k, p, v, x, other):
  put_keeps_others(t, L.good, k, p, v, x, other)
