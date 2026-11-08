# eukhe: the proof of LAW afw_answers_pass

import Base
import ../../bend/aux_fallback.bend as Af
import ../../bend/ffi_aux_fallback.bend as FAf
import ../../laws/aux_fallback/wire.bend as AuxFallbackWire
import ./base.bend as LA

def AuxFallbackWire.afw_answers_pass(r, sh, h):
  %LA.pfw.req(FAf.PassReq{r, sh}, "", h) : {FAf.ffi.go(_) == FAf.put_pass((Af.put(r, sh, Nil{}), Af.after(r, sh)), "") : String}
  {==}
