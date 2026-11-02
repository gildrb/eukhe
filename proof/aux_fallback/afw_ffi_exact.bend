# eukhe: the proof of LAW afw_ffi_exact
# The entry's decoder is the spec's reader stage by stage (LX.pxe.req),
# its answer the spec's reply (LX.pxe.answer: the model is the spec, the
# encoders the spec's spellers), its errors the spec's (LX.pxe.ffi).

import Base
import ../../bend/aux_fallback.bend as Af
import ../../bend/ffi_aux_fallback.bend as FAf
import ../../bend/wire.bend as Wr
import ../../laws/aux_fallback.bend as AuxFallback
import ./base/spec.bend as LX

def AuxFallback.afw_ffi_exact(s):
  LX.pxe.ffi(s)
