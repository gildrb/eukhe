# eukhe: the proof of LAW redirect_input_verify_same
#
# PROOF: the login's state equals itself (clm.str_refl), so the check keeps
# the paste.

import Base
import ../../bend/redirect_input.bend as Ri
import ../../laws/redirect_input.bend as RedirectInput
import ../call_lift/base/string.bend as LStr

def RedirectInput.redirect_input_verify_same(c, e):
  %Equal.sym(Bool, String.eq(e, e), True{}, LStr.clm.str_refl(e)) : {Ri.verify.at(_, c, e) == Ri.Pasted{c, Some{e}} : Ri.Answer}
  {==}
