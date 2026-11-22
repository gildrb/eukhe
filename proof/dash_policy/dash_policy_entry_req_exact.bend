# eukhe: the proof of LAW dash_policy_entry_req_exact
#
# PROOF: the decoder is the wire's string decoder: wire_str_exact gives the
# spelling, wire_str_decoded_fits the fit.

import Base
import ../../bend/ffi_dash_policy.bend as FDp
import ../../laws/dash_policy.bend as DashPolicy
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire
import ../wire/wire_str_exact.bend as PWireStrExact
import ../wire/wire_str_decoded_fits.bend as PWireStrDecodedFits

def DashPolicy.dash_policy_entry_req_exact(s, n, rest, h):
  (Wire.wire_str_exact(s, n, rest, h), Wire.wire_str_decoded_fits(s, n, rest, h))
