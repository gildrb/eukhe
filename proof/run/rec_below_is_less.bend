# eukhe: the proof of LAW rec_below_is_less
#
# PROOF: by induction on both numbers; Nat.is_lt compares them the same
# way (Nat.cmp).

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run/recover.bend as RunRecover

def rbl.go(a: Nat, b: Nat) -> {RnRecovery.below(a, b) == Nat.is_lt(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      rbl.go(p, q)

def RunRecover.rec_below_is_less(a, b):
  rbl.go(a, b)
