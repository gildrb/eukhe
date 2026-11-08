# eukhe: the proof of LAW deferred_step_exact

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ./base.bend as LA

def Retry.deferred_step_exact(fails, budget, job, got):
  LA.rp.job_step(fails, budget, job, got)
