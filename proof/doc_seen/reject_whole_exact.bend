# eukhe: the proof of LAW reject_whole_exact

import Base
import ../../bend/doc_seen.bend as Ds
import ../../laws/doc_seen.bend as DocSeen
import ./base.bend as LA

def pv.whole_go(+u: List<&2, Ds.At>) -> {Ds.Check.whole(Ds.check.go(u)) == DocSeen.seen.Whole(u) : Bool}:
  LA.pv.whole_eq(Nat.is_le(List.length(&2, Ds.At, u), Ds.cap), u)

def DocSeen.reject_whole_exact(seen, ats):
  %LA.pv.unseen_eq(seen, ats) : {Ds.Check.whole(Ds.check(seen, ats)) == DocSeen.seen.Whole(_) : Bool}
  pv.whole_go(Ds.unseen(seen, ats))
