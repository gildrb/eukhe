# eukhe: the proof of LAW tiny_ffi_malformed_unless_request
#
# PROOF: the decoder reads only spelled requests that fit, the rest after
# them untouched (tro.req of tiny_ffi_reads_only_requests); when it reads
# none the entry answers the malformed error, which the premise excludes.

import Base
import ../../bend/ffi_tiny.bend as FTn
import ../../bend/wire.bend as Wr
import ../../laws/tiny/pick.bend as Tiny
import ../wire/base/spell.bend as LAWireSpell
import ./tiny_ffi_reads_only_requests.bend as PTinyFfiReadsOnlyRequests

def tmu.goal(+s: String) -> Type:
  &q: FTn.Req -> &rest: String -> {(s, Tiny.tiny_req_fits(q)) == (Tiny.tiny_spell_req(q, rest), True{}) : String & Bool}

def tmu.eq(+s: String, +q: FTn.Req, +rest: String, e1: {s == Tiny.tiny_spell_req(q, rest) : String}, e2: {Tiny.tiny_req_fits(q) == True{} : Bool}) -> {(s, Tiny.tiny_req_fits(q)) == (Tiny.tiny_spell_req(q, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, Tiny.tiny_spell_req(q, rest), e1) : {(_, Tiny.tiny_req_fits(q)) == (Tiny.tiny_spell_req(q, rest), True{}) : String & Bool}
  %Equal.sym(Bool, Tiny.tiny_req_fits(q), True{}, e2) : {(Tiny.tiny_spell_req(q, rest), _) == (Tiny.tiny_spell_req(q, rest), True{}) : String & Bool}
  {==}

def tmu.main(+s: String, d: Wr.Dec<FTn.Req>, inv: PTinyFfiReadsOnlyRequests.tro.Req(s, d), other: {String.eq(FTn.answer(d), Wr.err("tiny: malformed request")) == False{} : Bool}) -> tmu.goal(s):
  match d:
    case Wr.Got{+q, +rest}:
      (e1, e2) = inv
      (q, (rest, tmu.eq(s, q, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(tmu.goal(s), other)

def Tiny.tiny_ffi_malformed_unless_request(s, other):
  tmu.main(s, FTn.get_req(s), PTinyFfiReadsOnlyRequests.tro.req(s), other)
