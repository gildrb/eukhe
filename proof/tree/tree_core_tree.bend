# eukhe: the proof of LAW tree_core_tree

import Base
import ../../bend/tree.bend as Tr
import ../../laws/tree.bend as Tree
import ./base/tree/misc.bend as LATreeMisc
import ./base/tree/sorted.bend as LATreeSorted

# The laws of the compiled core

def Tree.tree_core_tree(hs, rs):
  +M = Tr.KMap.go(rs, hs, Tr.KNil{})
  +L = List.reverse.go(&2, Tr.Rec, rs, Nil{})
  %Equal.sym(Tr.St, Tr.core.feed(hs, rs), Tr.St{M, L, hs}, LATreeMisc.tc.feed(hs, rs)) : {Tr.KMap.read(Tr.St.m(_)) == Tr.replay(rs) : List<&2, Tr.Ent>}
  LATreeSorted.tc.live_read(hs, rs)
