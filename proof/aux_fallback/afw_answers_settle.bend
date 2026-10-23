# eukhe: the proof of LAW afw_answers_settle

import Base
import ../../bend/aux_fallback.bend as Af
import ../../bend/ffi_aux_fallback.bend as FAf
import ../../laws/aux_fallback.bend as AuxFallback
import ./base.bend as LA

def AuxFallback.afw_answers_settle(g, look, need, h):
  %LA.pfw.req(FAf.SettleReq{g, look, need}, "", h) : {FAf.ffi.go(_) == FAf.put_route(Af.settle(g, look, need), "") : String}
  {==}
