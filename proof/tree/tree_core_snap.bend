# eukhe: the proof of LAW tree_core_snap

import Base
import ../../bend/tree.bend as Tr
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.tree_core_snap(hs, rs, n):
  +M = Tr.KMap.go(rs, hs, Tr.KNil{})
  +L = List.reverse.go(&2, Tr.Rec, rs, Nil{})
  +T = Tr.St.at(L, hs, n)
  +R2 = Tr.replay(List.take(&2, Tr.Rec, rs, n))
  %Equal.sym(Tr.St, Tr.core.feed(hs, rs), Tr.St{M, L, hs}, LA.tc.feed(hs, rs)) : {Pair.snd(Tr.St, Tr.Ans, Tr.core.step(_, Tr.Snap{n})) == Tr.Nodes{R2} : Tr.Ans}
  Equal.cong(List<&2, Tr.Ent>, Tr.Ans, z => Tr.Nodes{z}, Tr.KMap.onto(T, Nil{}), R2, Equal.trans(List<&2, Tr.Ent>, Tr.KMap.onto(T, Nil{}), Tr.KMap.read(T), R2, LA.tc.onto_nil(T), LA.tc.at_read(hs, rs, n)))
