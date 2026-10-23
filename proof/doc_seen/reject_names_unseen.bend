# eukhe: the proof of LAW reject_names_unseen

import Base
import ../../bend/doc_seen.bend as Ds
import ../../laws/doc_seen.bend as DocSeen
import ./base.bend as LA

def pv.names_go(+u: List<&2, Ds.At>) -> {Ds.Check.unseen(Ds.check.go(u)) == Ds.lines(u) : List<&2, Nat>}:
  {==}

def DocSeen.reject_names_unseen(seen, ats):
  %LA.pv.unseen_eq(seen, ats) : {Ds.Check.unseen(Ds.check(seen, ats)) == Ds.lines(_) : List<&2, Nat>}
  pv.names_go(Ds.unseen(seen, ats))
