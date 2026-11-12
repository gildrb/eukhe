# eukhe: the proof of LAW redirect_input_clean_trims_lead
#
# PROOF: a wrapping char is no noise, so the trim meets it first (LC.rcl.lead).

import Base
import ../../bend/redirect_input.bend as Ri
import ../../laws/redirect_input.bend as RedirectInput
import ./base/clean.bend as LC

def RedirectInput.redirect_input_clean_trims_lead(w, s, wrap):
  LC.rcl.lead(w, s, wrap)
