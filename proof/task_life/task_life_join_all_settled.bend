# eukhe: the proof of LAW task_life_join_all_settled
#
# PROOF: any is some (tlb.any), and allSettled's marks are none, the
# spec's (tlb.keep).

import Base
import ../../bend/task_life.bend as Tl
import ../../bend/ffi_task_life.bend as FTl
import ../../bend/submission.bend as Sb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../spec/durable/task_life.bend as Sp
import ../../laws/task_life.bend as TaskLife
import ./base.bend as LB

def TaskLife.task_life_join_all_settled(live, failed):
  %LB.tlb.any(live) : {Tl.join(Tl.AllSettled{}, live, failed) == (Bool.not(_), Sp.none_marked(live)) : Bool & List<&2, Bool>}
  %LB.tlb.keep(live) : {Tl.join(Tl.AllSettled{}, live, failed) == (Bool.not(Tl.any(live)), _) : Bool & List<&2, Bool>}
  {==}
