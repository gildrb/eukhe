# eukhe: the proof of LAW task_life_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left (tle.req),
# so the entry answers the rules' decision, encoded as the spec spells it
# (tlr.answer).

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

def TaskLife.task_life_entry_answers(q, fit):
  %LE.tle.req(q, "", fit) : {FTl.ffi.got(_) == SpW.w_reply(q) : String}
  LE.tlr.answer(q)
