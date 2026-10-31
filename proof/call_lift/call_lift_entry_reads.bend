# eukhe: the proof of LAW call_lift_entry_reads
#
# PROOF: the laws' reader reads a spelled request that fits back with nothing left (cle.req_rt), so the end check passes and the reader answers the calls.

import Base
import ../../bend/call_lift.bend as Cl
import ../../bend/wire.bend as Wr
import ../../spec/harness/lift_wire.bend as SpW
import ../../laws/call_lift.bend as CallLift
import ./base/entry.bend as LCallLiftEntry

def CallLift.call_lift_entry_reads(cs, fit):
  %Equal.sym(Wr.Dec<List<&2, Cl.Call>>, Wr.get_list(~Cl.Call, ~SpW.r_call, SpW.w_req(cs, "")), Wr.Got{cs, ""}, LCallLiftEntry.cle.req_rt(cs, "", fit)) : {SpW.r_whole(_) == Some{cs} : Maybe<&2, List<&2, Cl.Call>>}
  {==}
