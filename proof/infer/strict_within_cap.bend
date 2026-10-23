# eukhe: the proof of LAW strict_within_cap

import Base
import ../../bend/infer.bend as If
import ../../LAWS.bend as Laws
import ../base.bend as L

# The strict schema budget
# ------------------------

def pi.take_len(xs: List<&2, If.Tool>, n: Nat) -> {Nat.is_le(List.length(&2, If.Tool, List.take(&2, If.Tool, xs, n)), n) == True{} : Bool}:
  match xs n:
    case Nil{} _:
      L.pi.le0(n)
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      pi.take_len(t, p)

def pi.strict_within_cap(+cap: Nat, +ts: List<&2, If.Tool>) -> {Nat.is_le(List.length(&2, If.Tool, Pair.fst(List<&2, If.Tool>, List<&2, If.Tool>, If.strict(cap, ts))), cap) == True{} : Bool}:
  pi.take_len(If.rank(ts), cap)

def Laws.strict_within_cap(cap, ts):
  pi.strict_within_cap(cap, ts)
