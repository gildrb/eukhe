# eukhe: the proof of LAW redirect_input_entry_left_over
#
# PROOF: the spelled request reads back with the extra input left (rie.req_rt), which the entry refuses.

import Base
import ../../bend/redirect_input.bend as Ri
import ../../bend/ffi_redirect_input.bend as FRi
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/redirect_input.bend as RedirectInput
import ./base/entry.bend as LE

def RedirectInput.redirect_input_entry_left_over(q, c, t, fit):
  %Equal.sym(Wr.Dec<FRi.Req>, FRi.get_req(RedirectInput.ri_w_req(q, SCon{c, t})), Wr.Got{q, SCon{c, t}}, LE.rie.req_rt(q, SCon{c, t}, fit)) : {FRi.ffi.got(_) == Wr.err("redirect_input: malformed request") : String}
  {==}
