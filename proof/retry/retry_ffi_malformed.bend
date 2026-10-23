# eukhe: the proof of LAW retry_ffi_malformed

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_retry.bend as Fr
import ../../LAWS.bend as Laws

def Laws.retry_ffi_malformed(s, h):
  %Equal.sym(Wr.Dec<Fr.Req>, Fr.get_req(s), Wr.Bad{}, h) : {Fr.ffi.got(_) == Wr.err("retry: malformed request") : String}
  {==}
