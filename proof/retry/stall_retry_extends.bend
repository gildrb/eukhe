# eukhe: the proof of LAW stall_retry_extends

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base.bend as L

def rp.lt_add_succ(k: Nat, +j: Nat) -> {Nat.is_lt(k, Nat.add(k, 1n+j)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      rp.lt_add_succ(p, j)

# (R5) The stall
# --------------

def stall_extends(+idle: Nat, positive: {Nat.is_gt(idle, 0n) == True{} : Bool}) -> {Nat.is_lt(idle, R.stall.next(idle)) == True{} : Bool}:
  match idle:
    case 0n:
      L.rp.absurdF({Nat.is_lt(0n, R.stall.next(0n)) == True{} : Bool}, positive)
    case 1n+k:
      rp.lt_add_succ(k, k)

def Retry.stall_retry_extends(idle, positive):
  stall_extends(idle, positive)
