# eukhe: the proof of LAW retry_ffi_malformed

import Base
import ../../bend/ffi_retry.bend as Fr
import ../../bend/wire.bend as Wr
import ../../laws/retry.bend as Retry

def Retry.retry_ffi_malformed(s, h):
  %Equal.sym(Wr.Dec<Fr.Req>, Fr.get_req(s), Wr.Bad{}, h) : {Fr.ffi.got(_) == Wr.err("retry: malformed request") : String}
  {==}
