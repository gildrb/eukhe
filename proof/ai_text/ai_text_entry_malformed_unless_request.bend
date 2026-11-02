# eukhe: the proof of LAW ai_text_entry_malformed_unless_request
#
# PROOF: the Bad arm answers exactly the malformed error, which contradicts
# the premise; a request read is the spelling of a request that fits, then
# its rest (awe.rp_all).

import Base
import ../../bend/ffi_ai_text.bend as FT
import ../../bend/wire.bend as Wr
import ../../laws/ai_text.bend as AiText
import ../wire/base/spell.bend as LAWireSpell
import ./base/entry.bend as LE

def aitmu.G(s: String) -> Type:
  Sigma<&1, &1, FT.Req, q => Sigma<&1, &1, String, rest => {(s, AiText.sp_fit_req(q)) == (AiText.sp_w_req(q, rest), True{}) : String & Bool}>>

def aitmu.eq(+s: String, +q: FT.Req, +rest: String, e: {s == AiText.sp_w_req(q, rest) : String}, f: {AiText.sp_fit_req(q) == True{} : Bool}) -> {(s, AiText.sp_fit_req(q)) == (AiText.sp_w_req(q, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, AiText.sp_w_req(q, rest), e) : {(_, AiText.sp_fit_req(q)) == (AiText.sp_w_req(q, rest), True{}) : String & Bool}
  %Equal.sym(Bool, AiText.sp_fit_req(q), True{}, f) : {(AiText.sp_w_req(q, rest), _) == (AiText.sp_w_req(q, rest), True{}) : String & Bool}
  {==}

def aitmu.mu(+s: String, d: Wr.Dec<FT.Req>, rp: LE.aite.RP(s, d), other: {String.eq(FT.ffi.got(d), Wr.err("ai_text: malformed request")) == False{} : Bool}) -> aitmu.G(s):
  match d:
    case Wr.Got{+q, +rest}:
      (e, f) = rp
      (q, (rest, aitmu.eq(s, q, rest, e, f)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(aitmu.G(s), other)

def AiText.ai_text_entry_malformed_unless_request(s, other):
  aitmu.mu(s, FT.get_req(s), LE.aite.rp_all(s), other)
