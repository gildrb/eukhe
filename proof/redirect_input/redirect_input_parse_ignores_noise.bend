# eukhe: the proof of LAW redirect_input_parse_ignores_noise
#
# PROOF: the answer reads the cleaned text only (LC.rcl.parse), which drops the char (LC.rcl.noise).

import Base
import ../../bend/redirect_input.bend as Ri
import ../../laws/redirect_input.bend as RedirectInput
import ./base/clean.bend as LC

def RedirectInput.redirect_input_parse_ignores_noise(a, x, b, noise):
  LC.rcl.parse(String.append(a, SCon{x, b}), String.append(a, b), LC.rcl.noise(a, x, b, noise))
