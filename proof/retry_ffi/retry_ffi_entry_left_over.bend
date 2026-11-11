# eukhe: the proof of LAW retry_ffi_entry_left_over
# The laws' spelling is the entry's encoding (LARetryFfi.rf.req); a request
# that fits reads back with the input after it untouched
# (retry_ffi_request_round_trip), and that input is not the end.

import Base
import ../../bend/ffi_retry.bend as Fr
import ../../bend/wire.bend as Wr
import ../../laws/retry.bend as Retry
import ../../laws/retry_ffi.bend as RetryFfi
import ../retry/retry_ffi_request_round_trip.bend as PRetryFfiRequestRoundTrip
import ./base.bend as LARetryFfi

def rfl.left_over(+q: Fr.Req, +h: Char, +t: String, fits: {Retry.rs.req_fits(q) == True{} : Bool}) -> {Fr.ffi(RetryFfi.spell_req(q, SCon{h, t})) == Wr.err("retry: input left after the request") : String}:
  %Equal.sym(String, RetryFfi.spell_req(q, SCon{h, t}), Fr.put_req(q, SCon{h, t}), LARetryFfi.rf.req(q, SCon{h, t})) : {Fr.ffi(_) == Wr.err("retry: input left after the request") : String}
  %Equal.sym(Wr.Dec<Fr.Req>, Fr.get_req(Fr.put_req(q, SCon{h, t})), Wr.Got{q, SCon{h, t}}, Retry.retry_ffi_request_round_trip(q, SCon{h, t}, fits)) : {Fr.ffi.got(_) == Wr.err("retry: input left after the request") : String}
  {==}

def RetryFfi.retry_ffi_entry_left_over(q, h, t, fits):
  rfl.left_over(q, h, t, fits)
