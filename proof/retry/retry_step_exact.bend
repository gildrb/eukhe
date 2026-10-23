# eukhe: the proof of LAW retry_step_exact

import Base
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.retry_step_exact(base, attempt, cap):
  LA.rx.double(Nat.sub(attempt, 1n), base, cap)
