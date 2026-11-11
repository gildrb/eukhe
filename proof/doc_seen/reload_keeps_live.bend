# eukhe: the proof of LAW reload_keeps_live
#
# PROOF: a version equals itself (induction), so the record is kept.

import Base
import ../../bend/doc_seen.bend as Ds
import ../../laws/doc_seen.bend as DocSeen

def rkl.refl(x: Nat) -> {Nat.is_eq(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+k:
      rkl.refl(k)

def DocSeen.reload_keeps_live(live, s):
  %Equal.sym(Bool, Nat.is_eq(live, live), True{}, rkl.refl(live)) : {Ds.reload.put(Ds.Rec{live, s}, Nil{}, _) == [Ds.Rec{live, s}] : List<&2, Ds.Rec>}
  {==}
