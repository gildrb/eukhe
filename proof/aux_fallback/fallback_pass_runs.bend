# eukhe: the proof of LAW fallback_pass_runs
#
# PROOF: an admitted selector is looked up (the gate), and a found model
# that fits is routed (paf.fits of fallback_window_fits).

import Base
import ../../bend/aux_fallback.bend as Af
import ../../laws/aux_fallback/model.bend as AuxFallback
import ./fallback_window_fits.bend as PFits

def AuxFallback.fallback_pass_runs(p, s, w, need, fit):
  PFits.paf.fits(p, s, w, need, fit)
