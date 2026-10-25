# eukhe: the proof of LAW job_step_tick_exact

import Base
import ../../bend/job.bend as Jb
import ../../laws/job_step.bend as JobStep

def JobStep.job_step_tick_exact(cap, j):
  match j:
    case Jb.Live{k, d}:
      {==}
    case Jb.Ended{k, d, x}:
      {==}
