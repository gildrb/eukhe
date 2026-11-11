# eukhe: the proof of LAW infer_guard_periods_small
#
# PROOF: the eight windows below 8 compute; no window of 8 or more is
# below 8.

import Base
import ../../bend/infer.bend as If
import ../../laws/infer_guard.bend as InferGuard
import ./base.bend as LAGuard

def InferGuard.infer_guard_periods_small(k, lo):
  match k:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n+j:
      LAGuard.gb.lt_zero({If.periods(8n+j) == 1n : Nat}, j, lo)
