# eukhe: the proof of LAW screen_ffi_reads_only_requests
#
# PROOF: whatever the entry's decoder reads is the spelling of what it
# read, then its rest, and fits the wire (SX.sx.req); so an answer that is
# no error comes from a request read whole, nothing left (sro.fin), and is
# the spelled reply of the model's decision (SP.scsp.answer).

import Base
import ../../bend/ffi_screen.bend as FSc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/screen/interface.bend as Screen
import ../wire/base/spell.bend as LAWireSpell
import ./screen_ffi_answers_spelled/spell.bend as SP
import ./screen_ffi_reads_only_requests/exact.bend as SX

def sro.G(s: String, a: String) -> Type:
  Sigma<&1, &1, FSc.Req, q => {(s, (Screen.screen_req_fits(q), a)) == (Screen.screen_spell_req(q, ""), (True{}, Screen.screen_spell_answer(q))) : String & (Bool & String)}>

# a request read whole: the input, the fit and the answer are the spec's
def sro.top_eq(+s: String, +q: FSc.Req, +a: String, e: {s == Screen.screen_spell_req(q, "") : String}, f: {Screen.screen_req_fits(q) == True{} : Bool}, ea: {a == Screen.screen_spell_answer(q) : String}) -> {(s, (Screen.screen_req_fits(q), a)) == (Screen.screen_spell_req(q, ""), (True{}, Screen.screen_spell_answer(q))) : String & (Bool & String)}:
  %Equal.sym(String, s, Screen.screen_spell_req(q, ""), e) : {(_, (Screen.screen_req_fits(q), a)) == (Screen.screen_spell_req(q, ""), (True{}, Screen.screen_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(Bool, Screen.screen_req_fits(q), True{}, f) : {(Screen.screen_spell_req(q, ""), (_, a)) == (Screen.screen_spell_req(q, ""), (True{}, Screen.screen_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(String, a, Screen.screen_spell_answer(q), ea) : {(Screen.screen_spell_req(q, ""), (True{}, _)) == (Screen.screen_spell_req(q, ""), (True{}, Screen.screen_spell_answer(q))) : String & (Bool & String)}
  {==}

# the end check: nothing left answers the request, anything left is the
# error form
def sro.fin(+s: String, +q: FSc.Req, r: String, pre: {s == Screen.screen_spell_req(q, r) : String}, f: {Screen.screen_req_fits(q) == True{} : Bool}, ok: {LawsBase.wire_opens_err(FSc.ffi.whole(q, Wr.end(r))) == False{} : Bool}) -> sro.G(s, FSc.ffi.whole(q, Wr.end(r))):
  match r:
    case SNil{}:
      (q, sro.top_eq(s, q, FSc.answer(q), pre, f, SP.scsp.answer(q)))
    case SCon{x, y}:
      LAWireSpell.ws_absurd(sro.G(s, FSc.ffi.whole(q, False{})), ok)

def sro.main(+s: String, d: Wr.Dec<FSc.Req>, inv: SX.sx.Req(s, d), ok: {LawsBase.wire_opens_err(FSc.ffi.of(d)) == False{} : Bool}) -> sro.G(s, FSc.ffi.of(d)):
  match d:
    case Wr.Got{+q, +r}:
      (e, f) = inv
      sro.fin(s, q, r, e, f, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(sro.G(s, Wr.err("screen: malformed request")), ok)

def Screen.screen_ffi_reads_only_requests(s, ok):
  sro.main(s, FSc.get_req(s), SX.sx.req(s), ok)
