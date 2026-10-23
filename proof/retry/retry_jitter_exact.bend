# eukhe: the proof of LAW retry_jitter_exact

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base/bool/misc.bend as LBoolMisc

def jitter_exact(step: Nat, +draw: Nat, positive: {Nat.is_gt(step, 0n) == True{} : Bool}) -> {R.jitter.draw(step, draw) == Nat.mod(draw, step) : Nat}:
  match step:
    case 0n:
      LBoolMisc.rp.absurdF({R.jitter.draw(0n, draw) == Nat.mod(draw, 0n) : Nat}, positive)
    case 1n+p:
      {==}

def Retry.retry_jitter_exact(step, draw, positive):
  jitter_exact(step, draw, positive)
