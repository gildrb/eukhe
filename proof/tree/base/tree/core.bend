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
