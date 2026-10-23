# eukhe: the proof of LAW afw_left_over

import Base
import ../../bend/ffi_aux_fallback.bend as FAf
import ../../bend/wire.bend as Wr
import ../../laws/aux_fallback.bend as AuxFallback
import ./base.bend as LA

def AuxFallback.afw_left_over(x, c, rest, h):
  %LA.pfw.req(x, SCon{c, rest}, h) : {FAf.ffi.go(_) == Wr.err("aux_fallback: input left over") : String}
  {==}
