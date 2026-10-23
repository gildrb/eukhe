# eukhe: the proof of LAW kernel_lock_attempt_leaves_none

import Base
import ../../bend/kernel_local.bend as KL
import ../../LAWS.bend as Laws

# The bootstrap lock
# ------------------

def pk.attempt_leaves_none(l: KL.Lock) -> {KL.own_left(KL.attempt(l)) == 0n : Nat}:
  match l:
    case KL.Free{}:
      {==}
    case KL.Live{}:
      {==}
    case KL.Gone{}:
      {==}

def Laws.kernel_lock_attempt_leaves_none(l):
  pk.attempt_leaves_none(l)
