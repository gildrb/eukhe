# eukhe: the proof of LAW redirect_input_clean_trims_trail
#
# PROOF: the trim of the reversed text meets the wrapping char first, whatever the leading trim left (LC.rcl.trail).

import Base
import ../../bend/redirect_input.bend as Ri
import ../../laws/redirect_input.bend as RedirectInput
import ./base/clean.bend as LC

def RedirectInput.redirect_input_clean_trims_trail(s, w, wrap):
  LC.rcl.trail(s, w, wrap)
