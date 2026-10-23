# eukhe: the proof of LAW tree_core_plan_keeps

import Base
import ../../bend/tree.bend as Tr
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.tree_core_plan_keeps(hs, rs, n):
  +M = Tr.KMap.go(rs, hs, Tr.KNil{})
  +L = List.reverse.go(&2, Tr.Rec, rs, Nil{})
  %Equal.sym(Tr.St, Tr.core.feed(hs, rs), Tr.St{M, L, hs}, LA.tc.feed(hs, rs)) : {Pair.fst(Tr.St, Tr.Ans, Tr.core.step(_, Tr.Plan{n})) == _ : Tr.St}
  {==}
