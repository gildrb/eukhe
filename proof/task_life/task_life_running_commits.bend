# eukhe: the proof of LAW task_life_running_commits
#
# PROOF: every claim computes: a running task's commit takes the next
# state it names, an outcome by its hold, and a handover keeps c.

import Base
import ../../bend/task_life.bend as Tl
import ../../spec/durable/task_life.bend as Sp
import ../../laws/task_life.bend as TaskLife
import ./base.bend as LB

def TaskLife.task_life_running_commits(c, d, p, o, h):
  ({==}, ({==}, ({==}, ({==}, {==}))))
