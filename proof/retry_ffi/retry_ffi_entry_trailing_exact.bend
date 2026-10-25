# eukhe: the proof of LAW retry_ffi_entry_trailing_exact
# The entry decodes the request the laws' reader reads (LARetryFfi.rf.rq),
# then refuses the input left after it.

import Base
import ../../bend/ffi_retry.bend as Fr
import ../../bend/wire.bend as Wr
import ../../laws/retry_ffi.bend as RetryFfi
import ./base.bend as LARetryFfi

def RetryFfi.retry_ffi_entry_trailing_exact(s, q, rest, got, left):
  %Equal.trans(Wr.Dec<Fr.Req>, Wr.Got{q, rest}, RetryFfi.read_req.go(Wr.get_nat(s)), Fr.get_req.start(Wr.get_nat(s)), Equal.sym(Wr.Dec<Fr.Req>, RetryFfi.read_req(s), Wr.Got{q, rest}, got), LARetryFfi.rf.rq(Wr.get_nat(s))) : {Fr.ffi.got(_) == SCon{'E', SCon{' ', "retry: input left after the request"}} : String}
  %Equal.sym(Bool, Wr.end(rest), False{}, left) : {Fr.ffi.done(q, _) == SCon{'E', SCon{' ', "retry: input left after the request"}} : String}
  {==}
