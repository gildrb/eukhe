# eukhe: the proof of LAW aws_text_entry_reads_only_requests
#
# PROOF: whatever the decoder reads is the spelling of a request that fits,
# then its rest (awe.rp_all); an answer that is not the error form comes
# from a request read with nothing left, answered with the spelled model
# answer (awe.answer); the other arms answer the error form, which
# contradicts the premise (ws_absurd).

import Base
import ../../bend/ffi_aws_text.bend as FA
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/aws_text.bend as AwsText
import ../wire/base/spell.bend as LAWireSpell
import ./base/entry.bend as LE

def awro.top_eq(+s: String, +q: FA.Req, e: {s == AwsText.sp_w_req(q, "") : String}, f: {AwsText.sp_fit_req(q) == True{} : Bool}) -> {(s, (AwsText.sp_fit_req(q), FA.answer(q))) == (AwsText.sp_w_req(q, ""), (True{}, AwsText.sp_w_reply(q))) : String & (Bool & String)}:
  %Equal.sym(String, s, AwsText.sp_w_req(q, ""), e) : {(_, (AwsText.sp_fit_req(q), FA.answer(q))) == (AwsText.sp_w_req(q, ""), (True{}, AwsText.sp_w_reply(q))) : String & (Bool & String)}
  %Equal.sym(Bool, AwsText.sp_fit_req(q), True{}, f) : {(AwsText.sp_w_req(q, ""), (_, FA.answer(q))) == (AwsText.sp_w_req(q, ""), (True{}, AwsText.sp_w_reply(q))) : String & (Bool & String)}
  %Equal.sym(String, FA.answer(q), AwsText.sp_w_reply(q), LE.awe.answer(q)) : {(AwsText.sp_w_req(q, ""), (True{}, _)) == (AwsText.sp_w_req(q, ""), (True{}, AwsText.sp_w_reply(q))) : String & (Bool & String)}
  {==}

def awro.TopG(s: String, a: String) -> Type:
  Sigma<&1, &1, FA.Req, q => {(s, (AwsText.sp_fit_req(q), a)) == (AwsText.sp_w_req(q, ""), (True{}, AwsText.sp_w_reply(q))) : String & (Bool & String)}>

def awro.top(+s: String, d: Wr.Dec<FA.Req>, rp: LE.awe.RP(s, d), ok: {LawsBase.wire_opens_err(FA.ffi.got(d)) == False{} : Bool}) -> awro.TopG(s, FA.ffi.got(d)):
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (e, f) = rp
          (q, awro.top_eq(s, q, e, f))
        case SCon{x, y}:
          LAWireSpell.ws_absurd(awro.TopG(s, Wr.err("aws_text: malformed request")), ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(awro.TopG(s, Wr.err("aws_text: malformed request")), ok)

def AwsText.aws_text_entry_reads_only_requests(s, ok):
  awro.top(s, FA.get_req(s), LE.awe.rp_all(s), ok)
