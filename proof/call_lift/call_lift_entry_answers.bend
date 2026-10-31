# eukhe: the proof of LAW call_lift_entry_answers
#
# PROOF: the entry's decoder is the laws' reader (cle.req), which reads the spelled request back whole with nothing left (cle.req_rt), so the entry answers the count of the calls and their lifts by the shipped table, which are the spec's (call_lift_refines_spec), spelled by encoders that are the spec spellers (cle.answer).

import Base
import ../../bend/call_lift.bend as Cl
import ../../bend/ffi_call_lift.bend as FCl
import ../../bend/wire.bend as Wr
import ../../spec/harness/lift_wire.bend as SpW
import ../../laws/call_lift.bend as CallLift
import ./base/entry.bend as LCallLiftEntry
import ./base/read.bend as LCallLiftRead

def CallLift.call_lift_entry_answers(cs, fit):
  +s = SpW.w_req(cs, "")
  %Equal.sym(Wr.Dec<List<&2, Cl.Call>>, FCl.get_req(s), Wr.get_list(~Cl.Call, ~SpW.r_call, s), LCallLiftRead.cle.req(s)) : {FCl.ffi.got(_) == SpW.w_reply(cs) : String}
  %Equal.sym(Wr.Dec<List<&2, Cl.Call>>, Wr.get_list(~Cl.Call, ~SpW.r_call, s), Wr.Got{cs, ""}, LCallLiftEntry.cle.req_rt(cs, "", fit)) : {FCl.ffi.got(_) == SpW.w_reply(cs) : String}
  LCallLiftEntry.cle.answer(cs)
