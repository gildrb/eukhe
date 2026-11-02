# eukhe: the proof of LAW afw_ffi_spelled
# The spec's spelling is the entry's encoding (LX.pxe.put_req), which the
# entry reads back whole (afw_req_round_trip); its answer is the spec's
# reply (LX.pxe.answer).

import Base
import ../../bend/aux_fallback.bend as Af
import ../../bend/ffi_aux_fallback.bend as FAf
import ../../bend/wire.bend as Wr
import ../../laws/aux_fallback.bend as AuxFallback
import ./base/spec.bend as LX
import ./base.bend as LB

def AuxFallback.afw_ffi_spelled(x, h):
  %LX.pxe.put_req(x, "") : {FAf.ffi(_) == AuxFallback.afs_reply(x) : String}
  %Equal.sym(Wr.Dec<FAf.Req>, FAf.get_req(FAf.put_req(x, "")), Wr.Got{x, ""}, AuxFallback.afw_req_round_trip(x, "", h)) : {FAf.ffi.go(_) == AuxFallback.afs_reply(x) : String}
  LX.pxe.answer(x)
