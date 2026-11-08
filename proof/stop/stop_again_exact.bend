# eukhe: the proof of LAW stop_again_exact
#
# PROOF: with no round both are 1; after a round, case by case on whether
# its hash is h.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/stop.bend as Stop

def stp.again_at(eq: Bool, +k: Nat) -> {RnRecovery.again.eq(eq, k) == Stop.spec_again.at(eq, 1n+k) : Nat}:
  match eq:
    case True{}:
      {==}
    case False{}:
      {==}

def stp.again(+same: Nat, +last: Nat, +h: Nat) -> {RnRecovery.again(same, last, h) == Stop.spec_again(same, last, h) : Nat}:
  match same:
    case 0n:
      {==}
    case 1n+k:
      stp.again_at(Nat.is_eq(last, h), k)

def Stop.stop_again_exact(same, last, h):
  stp.again(same, last, h)
