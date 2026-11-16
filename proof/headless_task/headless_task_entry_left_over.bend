# eukhe: the proof of LAW headless_task_entry_left_over
#
# PROOF: the entry's decoder is the laws' reader (ht.req), which reads the
# spelled request back with the rest untouched (ht.req_rt); the rest is
# not empty, so the entry answers the error form.

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

def HeadlessTask.headless_task_entry_left_over(f, ch, t):
  +s = SpT.w_task_req(f, SCon{ch, t})
  %Equal.sym(Wr.Dec<Ht.Facts>, FHt.get_facts(s), SpT.r_task(s), LAHeadlessTask.ht.req(s)) : {FHt.ffi.got(_) == Wr.err("headless_task: malformed request") : String}
  %Equal.sym(Wr.Dec<Ht.Facts>, SpT.r_task(s), Wr.Got{f, SCon{ch, t}}, LAHeadlessTask.ht.req_rt(f, SCon{ch, t})) : {FHt.ffi.got(_) == Wr.err("headless_task: malformed request") : String}
  {==}
