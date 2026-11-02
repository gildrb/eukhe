# eukhe: the proof of LAW model_name_entry_reads_only_requests
#
# PROOF: whatever the decoder reads is the spelling of a request that fits,
# then its rest (mnx.rp_all); an answer that is not the error form comes
# from a request read with nothing left, answered with the spelled spec
# answer (mne.answer); the Bad and left-over arms answer the error form,
# which contradicts the premise (ws_absurd).

import Base
import ../../bend/ffi_model_name.bend as FM
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/model_name.bend as ModelName
import ../wire/base/spell.bend as LAWireSpell
import ./base/entry.bend as LE
import ./base/exact.bend as LX

def mnr.top_eq(+s: String, +q: FM.Req, e: {s == ModelName.sp_w_req(q, "") : String}, f: {ModelName.sp_fit_req(q) == True{} : Bool}) -> {(s, (ModelName.sp_fit_req(q), FM.answer(q))) == (ModelName.sp_w_req(q, ""), (True{}, ModelName.sp_w_reply(q))) : String & (Bool & String)}:
  %Equal.sym(String, s, ModelName.sp_w_req(q, ""), e) : {(_, (ModelName.sp_fit_req(q), FM.answer(q))) == (ModelName.sp_w_req(q, ""), (True{}, ModelName.sp_w_reply(q))) : String & (Bool & String)}
  %Equal.sym(Bool, ModelName.sp_fit_req(q), True{}, f) : {(ModelName.sp_w_req(q, ""), (_, FM.answer(q))) == (ModelName.sp_w_req(q, ""), (True{}, ModelName.sp_w_reply(q))) : String & (Bool & String)}
  %Equal.sym(String, FM.answer(q), ModelName.sp_w_reply(q), LE.mne.answer(q)) : {(ModelName.sp_w_req(q, ""), (True{}, _)) == (ModelName.sp_w_req(q, ""), (True{}, ModelName.sp_w_reply(q))) : String & (Bool & String)}
  {==}

def mnr.TopG(s: String, a: String) -> Type:
  Sigma<&1, &1, FM.Req, q => {(s, (ModelName.sp_fit_req(q), a)) == (ModelName.sp_w_req(q, ""), (True{}, ModelName.sp_w_reply(q))) : String & (Bool & String)}>

def mnr.top(+s: String, d: Wr.Dec<FM.Req>, rp: LX.mnx.RP(s, d), ok: {LawsBase.wire_opens_err(FM.ffi.got(d)) == False{} : Bool}) -> mnr.TopG(s, FM.ffi.got(d)):
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (e, f) = rp
          (q, mnr.top_eq(s, q, e, f))
        case SCon{x, y}:
          LAWireSpell.ws_absurd(mnr.TopG(s, Wr.err("model_name: malformed request")), ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(mnr.TopG(s, Wr.err("model_name: malformed request")), ok)

def ModelName.model_name_entry_reads_only_requests(s, ok):
  mnr.top(s, FM.get_req(s), LX.mnx.rp_all(s), ok)
