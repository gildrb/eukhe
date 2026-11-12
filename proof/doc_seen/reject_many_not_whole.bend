# eukhe: the proof of LAW reject_many_not_whole
#
# PROOF: more than 40 unseen anchors: the guard reads no width and answers
# not whole.

import Base
import ../../bend/doc_seen.bend as Ds
import ../../laws/doc_seen.bend as DocSeen
import ./base.bend as LA

def DocSeen.reject_many_not_whole(seen, ats, many):
  +u = Ds.unseen(seen, ats)
  %Equal.sym(Bool, Nat.is_le(List.length(&2, Ds.At, u), 40n), False{}, LA.dsr.le_unseen(seen, ats, 40n, False{}, many)) : {Ds.whole.go(_, u) == False{} : Bool}
  {==}
