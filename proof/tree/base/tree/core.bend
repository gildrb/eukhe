# eukhe: lemmas the proofs of area tree share: tree/core

import Base
import ../../../../bend/tree.bend as Tr
import ../pair.bend as LAPair

def tc.feed_go(rs: List<&2, Tr.Rec>, +m: Tr.KMap, +log: List<&2, Tr.Rec>, +hs: List<&2, Nat>) -> {Tr.core.feed.go(rs, Tr.St{m, log, hs}) == Tr.St{Tr.KMap.go(rs, hs, m), List.reverse.go(&2, Tr.Rec, rs, log), hs} : Tr.St}:
  match rs:
    case Nil{}:
      {==}
    case +r <> rest:
      +m2 = Pair.fst(Tr.KMap, Tr.Ans, Tr.KMap.rec(m, hs, r))
      %Equal.sym(Tr.St, Pair.fst(Tr.St, Tr.Ans, Tr.St.note(log, r, hs, Tr.KMap.rec(m, hs, r))), Tr.St{m2, r <> log, hs}, LAPair.tc.note_fst(log, r, hs, Tr.KMap.rec(m, hs, r))) : {Tr.core.feed.go(rest, _) == Tr.St{Tr.KMap.go(rest, hs, m2), List.reverse.go(&2, Tr.Rec, rest, r <> log), hs} : Tr.St}
      tc.feed_go(rest, m2, r <> log, hs)

# the stepper after a journal
def tc.feed(+hs: List<&2, Nat>, +rs: List<&2, Tr.Rec>) -> {Tr.core.feed(hs, rs) == Tr.St{Tr.KMap.go(rs, hs, Tr.KNil{}), List.reverse.go(&2, Tr.Rec, rs, Nil{}), hs} : Tr.St}:
  tc.feed_go(rs, Tr.KNil{}, Nil{}, hs)

def tc.feed_app(pre: List<&2, Tr.Rec>, +post: List<&2, Tr.Rec>, +s: Tr.St) -> {Tr.core.feed.go(List.append(&2, Tr.Rec, pre, post), s) == Tr.core.feed.go(post, Tr.core.feed.go(pre, s)) : Tr.St}:
  match pre:
    case Nil{}:
      {==}
    case +r <> rest:
      tc.feed_app(rest, post, Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Note{r})))

# a record steps the core to the core of the journal with the record at
# its end
def tc.note(+hs: List<&2, Nat>, +rs: List<&2, Tr.Rec>, +r: Tr.Rec) -> {Pair.fst(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), Tr.Note{r})) == Tr.core.feed(hs, List.append(&2, Tr.Rec, rs, [r])) : Tr.St}:
  +s = Tr.core.start(hs)
  Equal.sym(Tr.St, Tr.core.feed.go(List.append(&2, Tr.Rec, rs, [r]), s), Tr.core.feed.go([r], Tr.core.feed.go(rs, s)), tc.feed_app(rs, [r], s))

# a plan leaves the core as it was
def tc.plan_keeps(+hs: List<&2, Nat>, +rs: List<&2, Tr.Rec>, n: Nat) -> {Pair.fst(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), Tr.Plan{n})) == Tr.core.feed(hs, rs) : Tr.St}:
  +M = Tr.KMap.go(rs, hs, Tr.KNil{})
  +L = List.reverse.go(&2, Tr.Rec, rs, Nil{})
  %Equal.sym(Tr.St, Tr.core.feed(hs, rs), Tr.St{M, L, hs}, tc.feed(hs, rs)) : {Pair.fst(Tr.St, Tr.Ans, Tr.core.step(_, Tr.Plan{n})) == _ : Tr.St}
  {==}

# a snapshot leaves the core as it was
def tc.snap_keeps(+hs: List<&2, Nat>, +rs: List<&2, Tr.Rec>, n: Nat) -> {Pair.fst(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), Tr.Snap{n})) == Tr.core.feed(hs, rs) : Tr.St}:
  +M = Tr.KMap.go(rs, hs, Tr.KNil{})
  +L = List.reverse.go(&2, Tr.Rec, rs, Nil{})
  %Equal.sym(Tr.St, Tr.core.feed(hs, rs), Tr.St{M, L, hs}, tc.feed(hs, rs)) : {Pair.fst(Tr.St, Tr.Ans, Tr.core.step(_, Tr.Snap{n})) == _ : Tr.St}
  {==}
