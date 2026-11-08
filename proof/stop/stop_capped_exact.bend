# eukhe: the proof of LAW stop_capped_exact
#
# PROOF: kind by kind; the model's cap test is Nat's (stb.below).

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ./base.bend as LA
import ../../laws/stop.bend as Stop

def stp.capped(+rc: RnRecovery.RCfg, k: RnRecovery.Rk, +row: Nat) -> {RnRecovery.Rk.capped(rc, k, row) == Stop.spec_capped(rc, k, row) : Bool}:
  match rc:
    case RnRecovery.RCfg{+long, +leak, +redirect, +repeat}:
      match k:
        case RnRecovery.Free{}:
          {==}
        case RnRecovery.Longs{}:
          Equal.sym(Bool, Nat.is_lt(row, 2n+long), RnRecovery.below(row, 2n+long), LA.stb.below(row, 2n+long))
        case RnRecovery.Leaks{}:
          Equal.sym(Bool, Nat.is_lt(row, 1n+leak), RnRecovery.below(row, 1n+leak), LA.stb.below(row, 1n+leak))
        case RnRecovery.Loops{}:
          Equal.sym(Bool, Nat.is_lt(row, 1n+redirect), RnRecovery.below(row, 1n+redirect), LA.stb.below(row, 1n+redirect))
        case RnRecovery.Empties{}:
          Equal.sym(Bool, Nat.is_lt(row, 4n), RnRecovery.below(row, 4n), LA.stb.below(row, 4n))

def Stop.stop_capped_exact(rc, k, row):
  stp.capped(rc, k, row)
