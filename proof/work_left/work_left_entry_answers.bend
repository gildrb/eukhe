# eukhe: the proof of LAW work_left_entry_answers
#
# PROOF: the entry's decoder reads the spelled request back whole with
# nothing left (wl.req_rt: its counts fit the wire), so the entry answers
# the core's step, spelled as the spec spells it (wl.put).

import Base
import ../../bend/progress.bend as Pg
import ../../bend/work_left.bend as Wl
import ../../bend/ffi_work_left.bend as FWl
import ../../bend/wire.bend as Wr
import ../../spec/agents/work_left.bend as SpL
import ../../laws/work_left.bend as WorkLeft
import ./base.bend as LAWorkLeft


def WorkLeft.work_left_entry_answers(f, fits):
  +s = SpL.w_req(f, "")
  %Equal.sym(Wr.Dec<Wl.Facts>, FWl.get_facts(s), Wr.Got{f, ""}, LAWorkLeft.wl.req_rt(f, "", fits)) : {FWl.ffi.got(_) == SpL.w_step(Wl.decide(f), "") : String}
  LAWorkLeft.wl.put(Wl.decide(f), "")
