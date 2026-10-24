# eukhe: the proof of LAW retry_ffi_entry_malformed_exact
# The entry decodes every input as the laws' reader does (LARetryFfi.rf.rq):
# where that reader reads no request, the entry answers its error form.

import Base
import ../../bend/ffi_retry.bend as Fr
import ../../bend/wire.bend as Wr
import ../../laws/retry_ffi.bend as RetryFfi
import ./base.bend as LARetryFfi

def RetryFfi.retry_ffi_entry_malformed_exact(s, no):
  %Equal.trans(Wr.Dec<Fr.Req>, Wr.Bad{}, RetryFfi.read_req.go(Wr.get_nat(s)), Fr.get_req.start(Wr.get_nat(s)), Equal.sym(Wr.Dec<Fr.Req>, RetryFfi.read_req(s), Wr.Bad{}, no), LARetryFfi.rf.rq(Wr.get_nat(s))) : {Fr.ffi.got(_) == SCon{'E', SCon{' ', "retry: malformed request"}} : String}
  {==}
