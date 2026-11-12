# eukhe: the proof of LAW call_lift_entry_answers
#
# PROOF: the entry's decoder reads the spelled request back whole with nothing left (cle.req_rt), so the entry answers the count of the calls and their lifts by the shipped table, spelled by encoders that are the spec spellers (cle.answer).

import Base
import ../../bend/call_lift.bend as Cl
import ../../bend/ffi_call_lift.bend as FCl
import ../../bend/wire.bend as Wr
import ../../spec/harness/lift_wire.bend as SpW
import ../../laws/call_lift.bend as CallLift
import ./base/entry.bend as LCallLiftEntry

def CallLift.call_lift_entry_answers(cs, fit):
  %Equal.sym(Wr.Dec<List<&2, Cl.Call>>, FCl.get_req(SpW.w_req(cs, "")), Wr.Got{cs, ""}, LCallLiftEntry.cle.req_rt(cs, "", fit)) : {FCl.ffi.got(_) == SpW.w_reply(cs) : String}
  LCallLiftEntry.cle.answer(cs)
