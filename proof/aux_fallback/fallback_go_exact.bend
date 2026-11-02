# eukhe: the proof of LAW fallback_go_exact
# A session's events are the spec's fold, by induction on the passes
# (LX.pxe.session); a session starts with no key shown, so run is go from Nil.

import Base
import ../../bend/aux_fallback.bend as Af
import ../../bend/ffi_aux_fallback.bend as FAf
import ../../bend/wire.bend as Wr
import ../../laws/aux_fallback.bend as AuxFallback
import ./base/spec.bend as LX

def AuxFallback.fallback_go_exact(ps, sh, qs):
  (LX.pxe.session(ps, sh), LX.pxe.session(qs, Nil{}))
