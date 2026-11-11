# eukhe: the proof of LAW fallback_pass_too_small
#
# PROOF: an admitted selector is looked up (the gate), and a found model
# whose known window is smaller than the request falls back with reason 5
# (paf.small of fallback_window_small).

import Base
import ../../bend/aux_fallback.bend as Af
import ../../laws/aux_fallback/model.bend as AuxFallback
import ./fallback_window_small.bend as PSmall

def AuxFallback.fallback_pass_too_small(p, s, w, need, small):
  PSmall.paf.small(p, s, w, need, small)
