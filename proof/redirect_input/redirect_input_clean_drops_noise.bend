# eukhe: the proof of LAW redirect_input_clean_drops_noise
#
# PROOF: the drop removes the char where it is (LC.rcl.noise).

import Base
import ../../bend/redirect_input.bend as Ri
import ../../laws/redirect_input.bend as RedirectInput
import ./base/clean.bend as LC

def RedirectInput.redirect_input_clean_drops_noise(a, x, b, noise):
  LC.rcl.noise(a, x, b, noise)
