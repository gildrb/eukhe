# eukhe: the proof of LAW screen_ffi_answers_spelled
#
# PROOF: the spelled request is the entry's encoding (SP.scsp.req), which
# reads back whole (SP.scsp.rt); nothing is left, so the entry answers the
# model's decision, encoded: the spelled reply (SP.scsp.answer).

import Base
import ../../bend/ffi_screen.bend as FSc
import ../../bend/wire.bend as Wr
import ../../laws/screen.bend as Screen
import ./screen_ffi_answers_spelled/spell.bend as SP

def Screen.screen_ffi_answers_spelled(q, fits):
  %Equal.sym(String, Screen.screen_spell_req(q, ""), FSc.put_req(q, ""), SP.scsp.req(q, "")) : {FSc.ffi(_) == Screen.screen_spell_answer(q) : String}
  %Equal.sym(Wr.Dec<FSc.Req>, FSc.get_req(FSc.put_req(q, "")), Wr.Got{q, ""}, SP.scsp.rt(q, "", fits)) : {FSc.ffi.of(_) == Screen.screen_spell_answer(q) : String}
  SP.scsp.answer(q)
