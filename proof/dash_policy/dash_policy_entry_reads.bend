# eukhe: the proof of LAW dash_policy_entry_reads
#
# PROOF: the decoder is the wire's string decoder: wire_str_round_trip.

import Base
import ../../bend/ffi_dash_policy.bend as FDp
import ../../laws/dash_policy.bend as DashPolicy
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire

def DashPolicy.dash_policy_entry_reads(n, rest, h):
  Wire.wire_str_round_trip(n, rest, h)
