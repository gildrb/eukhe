# eukhe: the proof of LAW tree_snapshot_catches_up
#
# PROOF: the core's snapshot after the first n records is their replay
# (tree_core_snap); replaying the records after them on it is the replay
# of the first n records and then the rest (sc.go_append), which is the
# whole journal (sc.take_drop); the core's live tree is the journal's
# replay (tree_core_tree).

import Base
import ../../bend/tree.bend as Tr
import ../../laws/tree.bend as Tree
import ./tree_core_snap.bend as PTreeCoreSnap
import ./tree_core_tree.bend as PTreeCoreTree

def sc.go_append(pre: List<&2, Tr.Rec>, +post: List<&2, Tr.Rec>, +t: List<&2, Tr.Ent>) -> {Tr.go(post, Tr.go(pre, t)) == Tr.go(List.append(&2, Tr.Rec, pre, post), t) : List<&2, Tr.Ent>}:
  match pre:
    case Nil{}:
      {==}
    case +r <> rest:
      sc.go_append(rest, post, Tr.apply(t, r))

# the first n records, then the rest, are the records
def sc.take_drop(xs: List<&2, Tr.Rec>, n: Nat) -> {List.append(&2, Tr.Rec, List.take(&2, Tr.Rec, xs, n), List.drop(&2, Tr.Rec, xs, n)) == xs : List<&2, Tr.Rec>}:
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      Equal.cong(List<&2, Tr.Rec>, List<&2, Tr.Rec>, l => h <> l, List.append(&2, Tr.Rec, List.take(&2, Tr.Rec, t, p), List.drop(&2, Tr.Rec, t, p)), t, sc.take_drop(t, p))

def Tree.tree_snapshot_catches_up(hs, rs, n):
  +pre = List.take(&2, Tr.Rec, rs, n)
  +post = List.drop(&2, Tr.Rec, rs, n)
  +live = Tr.KMap.read(Tr.St.m(Tr.core.feed(hs, rs)))
  %Equal.sym(Tr.Ans, Pair.snd(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), Tr.Snap{n})), Tr.Nodes{Tr.replay(pre)}, Tree.tree_core_snap(hs, rs, n)) : {Tree.tree.catch_up(_, post) == Some{live} : Maybe<&2, List<&2, Tr.Ent>>}
  %Equal.sym(List<&2, Tr.Ent>, live, Tr.replay(rs), Tree.tree_core_tree(hs, rs)) : {Tree.tree.catch_up(Tr.Nodes{Tr.replay(pre)}, post) == Some{_} : Maybe<&2, List<&2, Tr.Ent>>}
  +e1 = sc.go_append(pre, post, Nil{})
  +e2 = Equal.cong(List<&2, Tr.Rec>, List<&2, Tr.Ent>, z => Tr.replay(z), List.append(&2, Tr.Rec, pre, post), rs, sc.take_drop(rs, n))
  Equal.cong(List<&2, Tr.Ent>, Maybe<&2, List<&2, Tr.Ent>>, z => Some{z}, Tr.go(post, Tr.replay(pre)), Tr.replay(rs), Equal.trans(List<&2, Tr.Ent>, Tr.go(post, Tr.replay(pre)), Tr.replay(List.append(&2, Tr.Rec, pre, post)), Tr.replay(rs), e1, e2))
