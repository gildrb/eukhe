# eukhe: the proof of LAW fallback_decide_exact
# The gate and the route compute the spec's on every case of the selector,
# the lookup and the window (LX.pxe.gate, LX.pxe.settle).

import Base
import ../../bend/aux_fallback.bend as Af
import ../../bend/ffi_aux_fallback.bend as FAf
import ../../bend/wire.bend as Wr
import ../../laws/aux_fallback.bend as AuxFallback
import ./base/spec.bend as LX

def AuxFallback.fallback_decide_exact(p, sel, ok, g, look, need):
  (LX.pxe.gate(p, sel, ok), LX.pxe.settle(g, look, need))
