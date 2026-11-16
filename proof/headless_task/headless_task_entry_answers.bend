# eukhe: the proof of LAW headless_task_entry_answers
#
# PROOF: the entry's decoder is the laws' reader (ht.req), which reads
# the spelled request back whole with nothing left (ht.req_rt), so the
# entry answers the core's exit, spelled as the spec spells it (ht.put).

import Base
import ../../bend/headless_exit.bend as Hx
import ../../bend/headless_task.bend as Ht
import ../../bend/ffi_headless_exit.bend as FHx
import ../../bend/ffi_headless_task.bend as FHt
import ../../bend/wire.bend as Wr
import ../../spec/durable/headless_wire.bend as SpW
import ../../spec/durable/headless_task.bend as SpT
import ../../laws/headless_task.bend as HeadlessTask
import ./base.bend as LAHeadlessTask

def HeadlessTask.headless_task_entry_answers(f):
  +s = SpT.w_task_req(f, "")
  %Equal.sym(Wr.Dec<Ht.Facts>, FHt.get_facts(s), SpT.r_task(s), LAHeadlessTask.ht.req(s)) : {FHt.ffi.got(_) == SpT.w_verdict(Ht.decide(f), "") : String}
  %Equal.sym(Wr.Dec<Ht.Facts>, SpT.r_task(s), Wr.Got{f, ""}, LAHeadlessTask.ht.req_rt(f, "")) : {FHt.ffi.got(_) == SpT.w_verdict(Ht.decide(f), "") : String}
  LAHeadlessTask.ht.put(Ht.decide(f), "")
