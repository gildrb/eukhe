# eukhe: the proof of LAW task_life_held_steps
#
# PROOF: every claim computes: a held task refuses all but a finalize,
# which keeps o held or makes it terminal by the hold.

import Base
import ../../bend/task_life.bend as Tl
import ../../spec/durable/task_life.bend as Sp
import ../../laws/task_life.bend as TaskLife
import ./base.bend as LB

def TaskLife.task_life_held_steps(o, n, q, h):
  ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))
