# eukhe: the proof of LAW model_name_entry_malformed_unless_request
#
# PROOF: the Bad arm answers exactly the malformed error, which contradicts
# the premise; a request read is the spelling of a request that fits, then
# its rest (mnx.rp_all).

import Base
import ../../bend/ffi_model_name.bend as FM
import ../../bend/wire.bend as Wr
import ../../laws/model_name.bend as ModelName
import ../wire/base/spell.bend as LAWireSpell
import ./base/exact.bend as LX

def mnm.MuG(s: String) -> Type:
  Sigma<&1, &1, FM.Req, q => Sigma<&1, &1, String, rest => {(s, ModelName.sp_fit_req(q)) == (ModelName.sp_w_req(q, rest), True{}) : String & Bool}>>

def mnm.mu_eq(+s: String, +q: FM.Req, +rest: String, e: {s == ModelName.sp_w_req(q, rest) : String}, f: {ModelName.sp_fit_req(q) == True{} : Bool}) -> {(s, ModelName.sp_fit_req(q)) == (ModelName.sp_w_req(q, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, ModelName.sp_w_req(q, rest), e) : {(_, ModelName.sp_fit_req(q)) == (ModelName.sp_w_req(q, rest), True{}) : String & Bool}
  %Equal.sym(Bool, ModelName.sp_fit_req(q), True{}, f) : {(ModelName.sp_w_req(q, rest), _) == (ModelName.sp_w_req(q, rest), True{}) : String & Bool}
  {==}

def mnm.mu(+s: String, d: Wr.Dec<FM.Req>, rp: LX.mnx.RP(s, d), other: {String.eq(FM.ffi.got(d), Wr.err("model_name: malformed request")) == False{} : Bool}) -> mnm.MuG(s):
  match d:
    case Wr.Got{+q, +rest}:
      (e, f) = rp
      (q, (rest, mnm.mu_eq(s, q, rest, e, f)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(mnm.MuG(s), other)

def ModelName.model_name_entry_malformed_unless_request(s, other):
  mnm.mu(s, FM.get_req(s), LX.mnx.rp_all(s), other)
