# eukhe: the proof of LAW fallback_pass_exact
# A pass's events and shown keys are the spec's: the model's membership is
# the spec's (LX.pxe.shown), then a case on the route.

import Base
import ../../bend/aux_fallback.bend as Af
import ../../bend/ffi_aux_fallback.bend as FAf
import ../../bend/wire.bend as Wr
import ../../laws/aux_fallback.bend as AuxFallback
import ./base/spec.bend as LX

def AuxFallback.fallback_pass_exact(r, sh):
  (LX.pxe.put(r, sh), LX.pxe.after(r, sh))
