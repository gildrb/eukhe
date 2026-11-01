# eukhe: the proof of LAW wait_any_entry_reads
#
# PROOF: the reader reads the spelled request back with nothing left (wa.req_rt), and the end check passes on the empty rest.

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny
import ./base.bend as LW
import ../../bend/ffi_wait_any.bend as FWa
import ../../bend/wire.bend as Wr
import ../../spec/durable/wait_any_wire.bend as SpW

def WaitAny.wait_any_entry_reads(q, fit):
  %Equal.sym(Wr.Dec<FWa.Req>, SpW.r_req(SpW.w_req(q, "")), Wr.Got{q, ""}, LW.wa.req_rt(q, "", fit)) : {SpW.r_whole(_) == Some{q} : Maybe<&2, FWa.Req>}
  {==}
