# eukhe: the proof of LAW reject_whole_exact

import Base
import ../../bend/doc_seen.bend as Ds
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pv.whole_go(+u: List<&2, Ds.At>) -> {Ds.Check.whole(Ds.check.go(u)) == Laws.seen.Whole(u) : Bool}:
  LA.pv.whole_eq(Nat.is_le(List.length(&2, Ds.At, u), Ds.cap), u)

def Laws.reject_whole_exact(seen, ats):
  %LA.pv.unseen_eq(seen, ats) : {Ds.Check.whole(Ds.check(seen, ats)) == Laws.seen.Whole(_) : Bool}
  pv.whole_go(Ds.unseen(seen, ats))
