# eukhe: the proof of LAW redirect_input_parse_ignores_wrappers
#
# PROOF: the answer reads the cleaned text only (LC.rcl.parse), which trims both chars (LC.rcl.wrapped).

import Base
import ../../bend/redirect_input.bend as Ri
import ../../laws/redirect_input.bend as RedirectInput
import ./base/clean.bend as LC

def RedirectInput.redirect_input_parse_ignores_wrappers(w1, s, w2, wrap1, wrap2):
  LC.rcl.parse(SCon{w1, String.append(s, SCon{w2, SNil{}})}, s, LC.rcl.wrapped(w1, s, w2, wrap1, wrap2))
