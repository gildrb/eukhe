# eukhe: the proof of LAW afw_answers_gate

import Base
import ../../bend/aux_fallback.bend as Af
import ../../bend/ffi_aux_fallback.bend as FAf
import ../../laws/aux_fallback/wire.bend as AuxFallbackWire
import ./base.bend as LA

def AuxFallbackWire.afw_answers_gate(p, sel, ok, h):
  %LA.pfw.req(FAf.GateReq{p, sel, ok}, "", h) : {FAf.ffi.go(_) == FAf.put_gate(Af.gate(p, sel, ok), "") : String}
  {==}
