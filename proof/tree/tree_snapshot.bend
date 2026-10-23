# eukhe: the proof of LAW tree_snapshot

import Base
import ../../bend/tree.bend as Tr
import ../../LAWS.bend as Laws

def pt.go_append(pre: List<&2, Tr.Rec>, +post: List<&2, Tr.Rec>, +t: List<&2, Tr.Ent>) -> {Tr.go(post, Tr.go(pre, t)) == Tr.go(List.append(&2, Tr.Rec, pre, post), t) : List<&2, Tr.Ent>}:
  match pre:
    case Nil{}:
      {==}
    case +r <> rest:
      pt.go_append(rest, post, Tr.apply(t, r))

def snapshot(+pre: List<&2, Tr.Rec>, +post: List<&2, Tr.Rec>) -> {Tr.go(post, Tr.replay(pre)) == Tr.replay(List.append(&2, Tr.Rec, pre, post)) : List<&2, Tr.Ent>}:
  pt.go_append(pre, post, Nil{})

def Laws.tree_snapshot(pre, post):
  snapshot(pre, post)
