# eukhe: the proof of LAW job_tick_changes_nothing
# The entry answers a tick with the job it got and no end.

import Base
import ../../bend/job.bend as Jb
import ../../laws/job_step.bend as JobStep
import ./base.bend as LA

def JobStep.job_tick_changes_nothing(t, cap, j, es):
  match j:
    case Jb.Live{k, d}:
      ({==}, {==})
    case Jb.Ended{k, d, x}:
      ({==}, {==})
