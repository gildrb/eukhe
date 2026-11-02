# eukhe: the proof of LAW ai_text_entry_reads_only_requests
#
# PROOF: whatever the decoder reads is the spelling of a request that fits,
# then its rest (awe.rp_all); an answer that is not the error form comes
# from a request read with nothing left, answered with the spelled model
# answer (awe.answer); the other arms answer the error form, which
# contradicts the premise (ws_absurd).

import Base
import ../../bend/ffi_ai_text.bend as FT
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/ai_text.bend as AiText
import ../wire/base/spell.bend as LAWireSpell
import ./base/entry.bend as LE

def aitro.top_eq(+s: String, +q: FT.Req, e: {s == AiText.sp_w_req(q, "") : String}, f: {AiText.sp_fit_req(q) == True{} : Bool}) -> {(s, (AiText.sp_fit_req(q), FT.answer(q))) == (AiText.sp_w_req(q, ""), (True{}, AiText.sp_w_reply(q))) : String & (Bool & String)}:
  %Equal.sym(String, s, AiText.sp_w_req(q, ""), e) : {(_, (AiText.sp_fit_req(q), FT.answer(q))) == (AiText.sp_w_req(q, ""), (True{}, AiText.sp_w_reply(q))) : String & (Bool & String)}
  %Equal.sym(Bool, AiText.sp_fit_req(q), True{}, f) : {(AiText.sp_w_req(q, ""), (_, FT.answer(q))) == (AiText.sp_w_req(q, ""), (True{}, AiText.sp_w_reply(q))) : String & (Bool & String)}
  %Equal.sym(String, FT.answer(q), AiText.sp_w_reply(q), LE.aite.answer(q)) : {(AiText.sp_w_req(q, ""), (True{}, _)) == (AiText.sp_w_req(q, ""), (True{}, AiText.sp_w_reply(q))) : String & (Bool & String)}
  {==}

def aitro.TopG(s: String, a: String) -> Type:
  Sigma<&1, &1, FT.Req, q => {(s, (AiText.sp_fit_req(q), a)) == (AiText.sp_w_req(q, ""), (True{}, AiText.sp_w_reply(q))) : String & (Bool & String)}>

def aitro.top(+s: String, d: Wr.Dec<FT.Req>, rp: LE.aite.RP(s, d), ok: {LawsBase.wire_opens_err(FT.ffi.got(d)) == False{} : Bool}) -> aitro.TopG(s, FT.ffi.got(d)):
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (e, f) = rp
          (q, aitro.top_eq(s, q, e, f))
        case SCon{x, y}:
          LAWireSpell.ws_absurd(aitro.TopG(s, Wr.err("ai_text: malformed request")), ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(aitro.TopG(s, Wr.err("ai_text: malformed request")), ok)

def AiText.ai_text_entry_reads_only_requests(s, ok):
  aitro.top(s, FT.get_req(s), LE.aite.rp_all(s), ok)
