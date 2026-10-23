# eukhe: the proof of LAW retry_step_exact

import Base
import ../../laws/retry.bend as Retry
import ./base.bend as LA

def Retry.retry_step_exact(base, attempt, cap):
  LA.rx.double(Nat.sub(attempt, 1n), base, cap)
