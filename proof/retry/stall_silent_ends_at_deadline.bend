# eukhe: the proof of LAW stall_silent_ends_at_deadline

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry

def silent_at_deadline(+d: Nat) -> {R.idle(Nil{}, d) == R.IdleStall{d} : R.Idle}:
  {==}

def Retry.stall_silent_ends_at_deadline(d):
  silent_at_deadline(d)
