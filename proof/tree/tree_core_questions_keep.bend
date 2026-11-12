# eukhe: the proof of LAW tree_core_questions_keep
#
# PROOF: from the core of any journal rs, the asks qs reach the core of rs
# followed by the records of qs (qk.go, by induction on qs): a record steps
# the core of rs to the core of rs with it at its end (tc.note), a plan or
# a snapshot leaves it as it was (tc.plan_keeps, tc.snap_keeps). From the
# open (rs empty) that is the core of the records of qs, so every next ask
# answers the same.

import Base
import ../../bend/tree.bend as Tr
import ../../laws/tree.bend as Tree
import ./base/tree/core.bend as LATreeCore
import ./base/list.bend as LATreeList

def qk.app_snoc(A: List<&2, Tr.Rec>, +r: Tr.Rec, +C: List<&2, Tr.Rec>) -> {List.append(&2, Tr.Rec, List.append(&2, Tr.Rec, A, [r]), C) == List.append(&2, Tr.Rec, A, r <> C) : List<&2, Tr.Rec>}:
  match A:
    case Nil{}:
      {==}
    case +a <> +t:
      Equal.cong(List<&2, Tr.Rec>, List<&2, Tr.Rec>, l => a <> l, List.append(&2, Tr.Rec, List.append(&2, Tr.Rec, t, [r]), C), List.append(&2, Tr.Rec, t, r <> C), qk.app_snoc(t, r, C))

# the asks qs from the core of rs reach the core of rs and their records
def qk.go(qs: List<&2, Tr.Ask>, +hs: List<&2, Nat>, +rs: List<&2, Tr.Rec>) -> {Tree.tree.asks(qs, Tr.core.feed(hs, rs)) == Tr.core.feed(hs, List.append(&2, Tr.Rec, rs, Tree.tree.notes(qs))) : Tr.St}:
  match qs:
    case Nil{}:
      Equal.cong(List<&2, Tr.Rec>, Tr.St, z => Tr.core.feed(hs, z), rs, List.append(&2, Tr.Rec, rs, Nil{}), Equal.sym(List<&2, Tr.Rec>, List.append(&2, Tr.Rec, rs, Nil{}), rs, LATreeList.tc.app_nil_rec(rs)))
    case q <> +rest:
      match q:
        case Tr.Note{+r}:
          +R = List.append(&2, Tr.Rec, rs, [r])
          %Equal.sym(Tr.St, Pair.fst(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), Tr.Note{r})), Tr.core.feed(hs, R), LATreeCore.tc.note(hs, rs, r)) : {Tree.tree.asks(rest, _) == Tr.core.feed(hs, List.append(&2, Tr.Rec, rs, r <> Tree.tree.notes(rest))) : Tr.St}
          %qk.app_snoc(rs, r, Tree.tree.notes(rest)) : {Tree.tree.asks(rest, Tr.core.feed(hs, R)) == Tr.core.feed(hs, _) : Tr.St}
          qk.go(rest, hs, R)
        case Tr.Plan{+n}:
          %Equal.sym(Tr.St, Pair.fst(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), Tr.Plan{n})), Tr.core.feed(hs, rs), LATreeCore.tc.plan_keeps(hs, rs, n)) : {Tree.tree.asks(rest, _) == Tr.core.feed(hs, List.append(&2, Tr.Rec, rs, Tree.tree.notes(rest))) : Tr.St}
          qk.go(rest, hs, rs)
        case Tr.Snap{+n}:
          %Equal.sym(Tr.St, Pair.fst(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), Tr.Snap{n})), Tr.core.feed(hs, rs), LATreeCore.tc.snap_keeps(hs, rs, n)) : {Tree.tree.asks(rest, _) == Tr.core.feed(hs, List.append(&2, Tr.Rec, rs, Tree.tree.notes(rest))) : Tr.St}
          qk.go(rest, hs, rs)

def Tree.tree_core_questions_keep(hs, qs, q):
  %qk.go(qs, hs, Nil{}) : {Pair.snd(Tr.St, Tr.Ans, Tr.core.step(Tree.tree.asks(qs, Tr.core.start(hs)), q)) == Pair.snd(Tr.St, Tr.Ans, Tr.core.step(_, q)) : Tr.Ans}
  {==}
