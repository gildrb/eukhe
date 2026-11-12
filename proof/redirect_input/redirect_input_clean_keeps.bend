# eukhe: the proof of LAW redirect_input_clean_keeps
#
# PROOF: the drop keeps a quiet text and the trims meet no wrapper (LC.rcl.keeps).

import Base
import ../../bend/redirect_input.bend as Ri
import ../../laws/redirect_input.bend as RedirectInput
import ./base/clean.bend as LC

def RedirectInput.redirect_input_clean_keeps(x, t, quiet, head, last):
  LC.rcl.keeps(x, t, quiet, head, last)
