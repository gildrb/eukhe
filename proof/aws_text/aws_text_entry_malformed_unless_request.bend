# eukhe: the proof of LAW aws_text_entry_malformed_unless_request
#
# PROOF: the Bad arm answers exactly the malformed error, which contradicts
# the premise; a request read is the spelling of a request that fits, then
# its rest (awe.rp_all).

import Base
import ../../bend/ffi_aws_text.bend as FA
import ../../bend/wire.bend as Wr
import ../../laws/aws_text.bend as AwsText
import ../wire/base/spell.bend as LAWireSpell
import ./base/entry.bend as LE

def awmu.G(s: String) -> Type:
  Sigma<&1, &1, FA.Req, q => Sigma<&1, &1, String, rest => {(s, AwsText.sp_fit_req(q)) == (AwsText.sp_w_req(q, rest), True{}) : String & Bool}>>

def awmu.eq(+s: String, +q: FA.Req, +rest: String, e: {s == AwsText.sp_w_req(q, rest) : String}, f: {AwsText.sp_fit_req(q) == True{} : Bool}) -> {(s, AwsText.sp_fit_req(q)) == (AwsText.sp_w_req(q, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, AwsText.sp_w_req(q, rest), e) : {(_, AwsText.sp_fit_req(q)) == (AwsText.sp_w_req(q, rest), True{}) : String & Bool}
  %Equal.sym(Bool, AwsText.sp_fit_req(q), True{}, f) : {(AwsText.sp_w_req(q, rest), _) == (AwsText.sp_w_req(q, rest), True{}) : String & Bool}
  {==}

def awmu.mu(+s: String, d: Wr.Dec<FA.Req>, rp: LE.awe.RP(s, d), other: {String.eq(FA.ffi.got(d), Wr.err("aws_text: malformed request")) == False{} : Bool}) -> awmu.G(s):
  match d:
    case Wr.Got{+q, +rest}:
      (e, f) = rp
      (q, (rest, awmu.eq(s, q, rest, e, f)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(awmu.G(s), other)

def AwsText.aws_text_entry_malformed_unless_request(s, other):
  awmu.mu(s, FA.get_req(s), LE.awe.rp_all(s), other)
