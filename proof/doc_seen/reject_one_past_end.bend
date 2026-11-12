# eukhe: the proof of LAW reject_one_past_end
#
# PROOF: the anchor's line is not seen (the guard's membership is the
# spec's), so it is the one unseen anchor, and the verdict computes.

import Base
import ../../bend/doc_seen.bend as Ds
import ../../laws/doc_seen.bend as DocSeen
import ./base.bend as LA

def DocSeen.reject_one_past_end(seen, n, u):
  %Equal.sym(Bool, Ds.mem(n, seen), False{}, LA.dsr.mem_is(n, seen, False{}, u)) : {Ds.check.go(Ds.unseen.put(Ds.At{n, None{}}, Nil{}, _)) == Ds.Check{[n], [], False{}} : Ds.Check}
  {==}
