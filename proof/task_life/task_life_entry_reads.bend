# eukhe: the proof of LAW task_life_entry_reads
#
# PROOF: the laws' reader is the entry's decoder (ter.req), which reads a
# spelled request back with nothing left (tle.req).

import Base
import ../../bend/task_life.bend as Tl
import ../../bend/ffi_task_life.bend as FTl
import ../../bend/submission.bend as Sb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../spec/durable/task_life_wire.bend as SpW
import ../../laws/task_life.bend as TaskLife
import ./base/entry.bend as LE
import ./base/read.bend as LR

def TaskLife.task_life_entry_reads(q, fit):
  %LR.ter.req(Wr.get_nat(SpW.w_req(q, ""))) : {SpW.r_whole(_) == Some{q} : Maybe<&2, FTl.Req>}
  %LE.tle.req(q, "", fit) : {SpW.r_whole(_) == Some{q} : Maybe<&2, FTl.Req>}
  {==}
