# eukhe: the proof of LAW work_left_entry_left_over
#
# PROOF: the entry's decoder reads the spelled request back with the rest
# untouched (wl.req_rt: its counts fit the wire); the rest is not empty,
# so the entry answers the error form.

import Base
import ../../bend/progress.bend as Pg
import ../../bend/work_left.bend as Wl
import ../../bend/ffi_work_left.bend as FWl
import ../../bend/wire.bend as Wr
import ../../spec/agents/work_left.bend as SpL
import ../../laws/work_left.bend as WorkLeft
import ./base.bend as LAWorkLeft


def WorkLeft.work_left_entry_left_over(f, fits, ch, t):
  +s = SpL.w_req(f, SCon{ch, t})
  %Equal.sym(Wr.Dec<Wl.Facts>, FWl.get_facts(s), Wr.Got{f, SCon{ch, t}}, LAWorkLeft.wl.req_rt(f, SCon{ch, t}, fits)) : {FWl.ffi.got(_) == Wr.err("work_left: malformed request") : String}
  {==}
