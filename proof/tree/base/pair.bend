# eukhe: lemmas the proofs of area tree share: pair

import Base
import ../../../bend/tree.bend as Tr
import ./logic.bend as LALogic

def tc.keep_case_bst2(b: Bool, +m: Tr.KMap, +n: Tr.KMap, +bm: {LALogic.tc.mpok(m) == True{} : Bool}, +bn: {LALogic.tc.mpok(n) == True{} : Bool}) -> {LALogic.tc.mpok(Pair.fst(Tr.KMap, Tr.Ans, Tr.keep.ans(b, m, n))) == True{} : Bool}:
  match b:
    case True{}:
      bn
    case False{}:
      bm

def tc.note_fst(+log: List<&2, Tr.Rec>, +r: Tr.Rec, +hs: List<&2, Nat>, p: Tr.KMap & Tr.Ans) -> {Pair.fst(Tr.St, Tr.Ans, Tr.St.note(log, r, hs, p)) == Tr.St{Pair.fst(Tr.KMap, Tr.Ans, p), r <> log, hs} : Tr.St}:
  match p:
    case Tuple{a, b}:
      {==}
