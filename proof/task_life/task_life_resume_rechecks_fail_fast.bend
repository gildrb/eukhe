# eukhe: the proof of LAW task_life_resume_rechecks_fail_fast
#
# PROOF: it computes.

import Base
import ../../bend/task_life.bend as Tl
import ../../spec/durable/task_life.bend as Sp
import ../../laws/task_life.bend as TaskLife
import ./base.bend as LB

def TaskLife.task_life_resume_rechecks_fail_fast(c):
  {==}
