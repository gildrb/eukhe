# eukhe: the proof of LAW reject_one_seen
#
# PROOF: the anchor's line is seen (the guard's membership is the spec's),
# so no anchor is unseen and the verdict on no anchor computes.

import Base
import ../../bend/doc_seen.bend as Ds
import ../../laws/doc_seen.bend as DocSeen
import ./base.bend as LA

def DocSeen.reject_one_seen(seen, n, w, s):
  %Equal.sym(Bool, Ds.mem(n, seen), True{}, LA.dsr.mem_is(n, seen, True{}, s)) : {Ds.check.go(Ds.unseen.put(Ds.At{n, w}, Nil{}, _)) == Ds.Check{[], [], True{}} : Ds.Check}
  {==}
