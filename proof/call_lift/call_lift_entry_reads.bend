# eukhe: the proof of LAW call_lift_entry_reads
#
# PROOF: the count reads back (wire_nat_round_trip), then each call, its family, rev and argument names (wire_str_round_trip, wire_strs_round_trip), leaving the input after them untouched (cle.req_rt, ./base/entry.bend).

import Base
import ../../bend/call_lift.bend as Cl
import ../../bend/ffi_call_lift.bend as FCl
import ../../bend/wire.bend as Wr
import ../../spec/harness/lift_wire.bend as SpW
import ../../laws/call_lift.bend as CallLift
import ./base/entry.bend as LCallLiftEntry

def CallLift.call_lift_entry_reads(cs, rest, fit):
  LCallLiftEntry.cle.req_rt(cs, rest, fit)
