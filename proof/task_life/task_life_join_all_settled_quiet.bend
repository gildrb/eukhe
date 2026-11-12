# eukhe: the proof of LAW task_life_join_all_settled_quiet
#
# PROOF: allSettled's marks are keep_all's, which count none
# (tlj.count_keep).

import Base
import ../../bend/task_life.bend as Tl
import ../../spec/durable/task_life.bend as Sp
import ../../laws/task_life.bend as TaskLife
import ./base.bend as LB
import ./base/join.bend as LJ

def TaskLife.task_life_join_all_settled_quiet(live, failed):
  LJ.tlj.count_keep(live)
