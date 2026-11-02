# eukhe: the proof of LAW aws_base64_valid_complete
#
# PROOF: the code's verdict is the spec's over the chunks' text (awq.decides);
# that text is b ++ e, of a length that is a multiple of 4, and valid
# (awq.valid_app).

import Base
import ../../bend/aws_text.bend as A
import ../../laws/aws_text.bend as AwsText
import ./base/b64.bend as LQ

def abc.spec(+b: String, +e: String, hb: {AwsText.sp_all_b64(b) == True{} : Bool}, he: {AwsText.sp_pad(e) == True{} : Bool}, hm: {AwsText.sp_mult4(AwsText.sp_units(String.append(b, e))) == True{} : Bool}) -> {AwsText.sp_base64(String.append(b, e)) == 0n : Nat}:
  %Equal.sym(Bool, AwsText.sp_mult4(AwsText.sp_units(String.append(b, e))), True{}, hm) : {AwsText.sp_b64_fin(_, AwsText.sp_valid(String.append(b, e))) == 0n : Nat}
  %Equal.sym(Bool, AwsText.sp_valid(String.append(b, e)), True{}, LQ.awq.valid_app(b, e, hb, he)) : {AwsText.sp_b64_fin(True{}, _) == 0n : Nat}
  {==}

def AwsText.aws_base64_valid_complete(cs, b, e, hc, hb, he, hm):
  +s = Equal.trans(Nat, AwsText.sp_base64(AwsText.sp_cat(cs)), AwsText.sp_base64(String.append(b, e)), 0n, Equal.cong(String, Nat, z => AwsText.sp_base64(z), AwsText.sp_cat(cs), String.append(b, e), hc), abc.spec(b, e, hb, he, hm))
  Equal.trans(Nat, A.base64(cs), AwsText.sp_base64(AwsText.sp_cat(cs)), 0n, LQ.awq.decides(cs), s)
