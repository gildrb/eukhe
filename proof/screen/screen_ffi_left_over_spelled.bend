# eukhe: the proof of LAW screen_ffi_left_over_spelled
#
# PROOF: the spelled request is the entry's encoding (SP.scsp.req), which
# reads back with the rest after it untouched (SP.scsp.rt); the rest is not
# empty, so the entry answers the left-over error form.

import Base
import ../../bend/ffi_screen.bend as FSc
import ../../bend/wire.bend as Wr
import ../../laws/screen/interface.bend as Screen
import ./screen_ffi_answers_spelled/spell.bend as SP

def Screen.screen_ffi_left_over_spelled(q, fits, c, t):
  %Equal.sym(String, Screen.screen_spell_req(q, SCon{c, t}), FSc.put_req(q, SCon{c, t}), SP.scsp.req(q, SCon{c, t})) : {FSc.ffi(_) == Wr.err("screen: input left over") : String}
  %Equal.sym(Wr.Dec<FSc.Req>, FSc.get_req(FSc.put_req(q, SCon{c, t})), Wr.Got{q, SCon{c, t}}, SP.scsp.rt(q, SCon{c, t}, fits)) : {FSc.ffi.of(_) == Wr.err("screen: input left over") : String}
  {==}
