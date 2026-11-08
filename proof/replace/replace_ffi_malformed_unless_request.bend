# eukhe: the proof of LAW replace_ffi_malformed_unless_request
#
# PROOF of LAW replace_ffi_malformed_unless_request: the decoder reads
# only spelled requests that fit, the rest after them untouched (rfo.all
# of replace_ffi_reads_only_requests); when it reads none the entry
# answers the malformed error, which the premise excludes.

import Base
import ../../bend/ffi_replace.bend as FRp
import ../../bend/wire.bend as Wr
import ../../laws/replace.bend as Replace
import ../wire/base/spell.bend as LAWireSpell
import ./replace_ffi_reads_only_requests.bend as PReplaceFfiReadsOnlyRequests

def rfm.goal(+s: String) -> Type:
  &q: FRp.Req -> &rest: String -> {(s, Replace.rp_req_fits(q)) == (Replace.rp_spell_req(q, rest), True{}) : String & Bool}

def rfm.eq(+s: String, +q: FRp.Req, +rest: String, e1: {s == Replace.rp_spell_req(q, rest) : String}, e2: {Replace.rp_req_fits(q) == True{} : Bool}) -> {(s, Replace.rp_req_fits(q)) == (Replace.rp_spell_req(q, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, Replace.rp_spell_req(q, rest), e1) : {(_, Replace.rp_req_fits(q)) == (Replace.rp_spell_req(q, rest), True{}) : String & Bool}
  %Equal.sym(Bool, Replace.rp_req_fits(q), True{}, e2) : {(Replace.rp_spell_req(q, rest), _) == (Replace.rp_spell_req(q, rest), True{}) : String & Bool}
  {==}

def rfm.main(+s: String, d: Wr.Dec<FRp.Req>, inv: PReplaceFfiReadsOnlyRequests.rfo(s, d), other: {String.eq(FRp.ffi.of(d), Wr.err("replace: malformed request")) == False{} : Bool}) -> rfm.goal(s):
  match d:
    case Wr.Got{+q, +rest}:
      (e1, e2) = inv
      (q, (rest, rfm.eq(s, q, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(rfm.goal(s), other)

def Replace.replace_ffi_malformed_unless_request(s, other):
  rfm.main(s, FRp.get_req(s), PReplaceFfiReadsOnlyRequests.rfo.all(s), other)
