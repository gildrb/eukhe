# eukhe: the proof of LAW tree_put_sets

import Base
import ../../bend/tree.bend as Tr
import ../../laws/tree.bend as Tree
import ../base.bend as L
import ./base.bend as LA

# A put
# -----

def put_sets(+t: List<&2, Tr.Ent>, good: {Tr.sound(t) == True{} : Bool}, +k: Nat, +p: Nat, +v: Nat, fits: {Tr.ok(t, k, p) == True{} : Bool}) -> {Tr.get(Tr.apply(t, Tr.Do{Tr.Put{k, p, v}}), k) == Some{Tr.Ent{k, p, v}} : Maybe<&2, Tr.Ent>}:
  %Equal.sym(Bool, Tr.ok(t, k, p), True{}, fits) : {Tr.get(Tr.put.at(_, t, Tr.Ent{k, p, v}), k) == Some{Tr.Ent{k, p, v}} : Maybe<&2, Tr.Ent>}
  LA.pt.get_set_same(t, Tr.Ent{k, p, v})

def Tree.tree_put_sets(t, L.good, k, p, v, fits):
  put_sets(t, L.good, k, p, v, fits)
