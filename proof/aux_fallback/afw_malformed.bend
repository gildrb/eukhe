# eukhe: the proof of LAW afw_malformed

import Base
import ../../bend/ffi_aux_fallback.bend as FAf
import ../../bend/wire.bend as Wr
import ../../laws/aux_fallback.bend as AuxFallback

def AuxFallback.afw_malformed(s, h):
  %Equal.sym(Wr.Dec<FAf.Req>, FAf.get_req(s), Wr.Bad{}, h) : {FAf.ffi.go(_) == Wr.err("aux_fallback: malformed request") : String}
  {==}
