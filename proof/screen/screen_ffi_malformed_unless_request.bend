# eukhe: the proof of LAW screen_ffi_malformed_unless_request
#
# PROOF: the decoder reads only spelled requests that fit, the rest after
# them untouched (SX.sx.req); when it reads none the entry answers the
# malformed error, which the premise excludes.

import Base
import ../../bend/ffi_screen.bend as FSc
import ../../bend/wire.bend as Wr
import ../../laws/screen/interface.bend as Screen
import ../wire/base/spell.bend as LAWireSpell
import ./screen_ffi_reads_only_requests/exact.bend as SX

def smu.goal(+s: String) -> Type:
  &q: FSc.Req -> &rest: String -> {(s, Screen.screen_req_fits(q)) == (Screen.screen_spell_req(q, rest), True{}) : String & Bool}

def smu.eq(+s: String, +q: FSc.Req, +rest: String, e1: {s == Screen.screen_spell_req(q, rest) : String}, e2: {Screen.screen_req_fits(q) == True{} : Bool}) -> {(s, Screen.screen_req_fits(q)) == (Screen.screen_spell_req(q, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, Screen.screen_spell_req(q, rest), e1) : {(_, Screen.screen_req_fits(q)) == (Screen.screen_spell_req(q, rest), True{}) : String & Bool}
  %Equal.sym(Bool, Screen.screen_req_fits(q), True{}, e2) : {(Screen.screen_spell_req(q, rest), _) == (Screen.screen_spell_req(q, rest), True{}) : String & Bool}
  {==}

def smu.main(+s: String, d: Wr.Dec<FSc.Req>, inv: SX.sx.Req(s, d), other: {String.eq(FSc.ffi.of(d), Wr.err("screen: malformed request")) == False{} : Bool}) -> smu.goal(s):
  match d:
    case Wr.Got{+q, +rest}:
      (e1, e2) = inv
      (q, (rest, smu.eq(s, q, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(smu.goal(s), other)

def Screen.screen_ffi_malformed_unless_request(s, other):
  smu.main(s, FSc.get_req(s), SX.sx.req(s), other)
