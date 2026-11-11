# eukhe: the proof of LAW reload_drops_stale
#
# PROOF: the record's version is not the live one, so it is dropped.

import Base
import ../../bend/doc_seen.bend as Ds
import ../../laws/doc_seen.bend as DocSeen

def DocSeen.reload_drops_stale(live, t, s, ne):
  %Equal.sym(Bool, Nat.is_eq(t, live), False{}, ne) : {Ds.reload.put(Ds.Rec{t, s}, Nil{}, _) == [] : List<&2, Ds.Rec>}
  {==}
