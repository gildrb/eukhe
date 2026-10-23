# eukhe: the proof of LAW tree_core_note

import Base
import ../../bend/tree.bend as Tr
import ../../LAWS.bend as Laws

def tc.feed_app(pre: List<&2, Tr.Rec>, +post: List<&2, Tr.Rec>, +s: Tr.St) -> {Tr.core.feed.go(List.append(&2, Tr.Rec, pre, post), s) == Tr.core.feed.go(post, Tr.core.feed.go(pre, s)) : Tr.St}:
  match pre:
    case Nil{}:
      {==}
    case +r <> rest:
      tc.feed_app(rest, post, Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Note{r})))

def Laws.tree_core_note(hs, rs, r):
  +s = Tr.core.start(hs)
  Equal.sym(Tr.St, Tr.core.feed.go(List.append(&2, Tr.Rec, rs, [r]), s), Tr.core.feed.go([r], Tr.core.feed.go(rs, s)), tc.feed_app(rs, [r], s))
