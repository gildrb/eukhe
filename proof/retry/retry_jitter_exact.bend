# eukhe: the proof of LAW retry_jitter_exact

import Base
import ../../bend/retry.bend as R
import ../../LAWS.bend as Laws
import ../base.bend as L

def jitter_exact(step: Nat, +draw: Nat, positive: {Nat.is_gt(step, 0n) == True{} : Bool}) -> {R.jitter.draw(step, draw) == Nat.mod(draw, step) : Nat}:
  match step:
    case 0n:
      L.rp.absurdF({R.jitter.draw(0n, draw) == Nat.mod(draw, 0n) : Nat}, positive)
    case 1n+p:
      {==}

def Laws.retry_jitter_exact(step, draw, positive):
  jitter_exact(step, draw, positive)
