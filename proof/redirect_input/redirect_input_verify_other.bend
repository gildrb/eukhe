# eukhe: the proof of LAW redirect_input_verify_other
#
# PROOF: the states differ, so the check refuses.

import Base
import ../../bend/redirect_input.bend as Ri
import ../../laws/redirect_input.bend as RedirectInput

def RedirectInput.redirect_input_verify_other(c, s, e, differ):
  %Equal.sym(Bool, String.eq(s, e), False{}, differ) : {Ri.verify.at(_, c, s) == Ri.Failed{Ri.FMismatch{}} : Ri.Answer}
  {==}
