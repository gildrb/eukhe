# eukhe: the proof of LAW aws_base64_valid_sound
#
# PROOF: the code's verdict is the spec's (awq.decides); a spec verdict 0
# has a length that is a multiple of 4 and a valid text (awq.fin0); a
# valid text is base64 chars, then the padding (awq.valid_sp).

import Base
import ../../bend/aws_text.bend as A
import ../../laws/aws_text.bend as AwsText
import ./base/b64.bend as LQ

def abs.G(cs: List<&2, String>) -> Type:
  Sigma<&1, &1, String, b => Sigma<&1, &1, String, e => {AwsText.sp_cat(cs) == String.append(b, e) : String} & ({AwsText.sp_all_b64(b) == True{} : Bool} & ({AwsText.sp_pad(e) == True{} : Bool} & {AwsText.sp_mult4(AwsText.sp_units(AwsText.sp_cat(cs))) == True{} : Bool}))>>

def abs.vp(+t: String, ev: {AwsText.sp_valid(t) == True{} : Bool}) -> LQ.awq.VP(t, True{}):
  %ev : LQ.awq.VP(t, _)
  LQ.awq.valid_sp(t)

def abs.fin(-cs: List<&2, String>, em: {AwsText.sp_mult4(AwsText.sp_units(AwsText.sp_cat(cs))) == True{} : Bool}, vp: LQ.awq.VP(AwsText.sp_cat(cs), True{})) -> abs.G(cs):
  (+b, (+e, (eq, (ab, pe)))) = vp
  (b, (e, (eq, (ab, (pe, em)))))

def abs.pair(+cs: List<&2, String>, mv: {AwsText.sp_mult4(AwsText.sp_units(AwsText.sp_cat(cs))) == True{} : Bool} & {AwsText.sp_valid(AwsText.sp_cat(cs)) == True{} : Bool}) -> abs.G(cs):
  (em, ev) = mv
  abs.fin(cs, em, abs.vp(AwsText.sp_cat(cs), ev))

def AwsText.aws_base64_valid_sound(cs, h):
  +t = AwsText.sp_cat(cs)
  +h2 = Equal.trans(Nat, AwsText.sp_base64(t), A.base64(cs), 0n, Equal.sym(Nat, A.base64(cs), AwsText.sp_base64(t), LQ.awq.decides(cs)), h)
  abs.pair(cs, LQ.awq.fin0(AwsText.sp_mult4(AwsText.sp_units(t)), AwsText.sp_valid(t), h2))
