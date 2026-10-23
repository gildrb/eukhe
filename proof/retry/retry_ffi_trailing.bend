# eukhe: the proof of LAW retry_ffi_trailing

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_retry.bend as Fr
import ../../LAWS.bend as Laws

def Laws.retry_ffi_trailing(s, q, rest, h, left):
  %Equal.sym(Wr.Dec<Fr.Req>, Fr.get_req(s), Wr.Got{q, rest}, h) : {Fr.ffi.got(_) == Wr.err("retry: input left after the request") : String}
  %Equal.sym(Bool, Wr.end(rest), False{}, left) : {Fr.ffi.done(q, _) == Wr.err("retry: input left after the request") : String}
  {==}
