# eukhe: the proof of LAW aws_rid_sound
#
# PROOF: what `x-` strips off leaves (mnb.sp) is M then a tail, M one or
# more word chars or `-` (awb.rid_sp).

import Base
import ../../bend/model_name.bend as M
import ../../bend/aws_text.bend as A
import ../../laws/aws_text.bend as AwsText
import ../model_name/base.bend as LA
import ./base.bend as LB

def aws.G(name: String) -> Type:
  Sigma<&1, &1, String, m => Sigma<&1, &1, Bool, k => {name == String.append("x-", String.append(m, AwsText.sp_rid_tail(k))) : String} & {AwsText.sp_wds(m) == True{} : Bool}>>

def aws.fin(-name: String, +r: String, v: {name == String.append("x-", r) : String}, rp: LB.awb.RidP(r, False{}, True{})) -> aws.G(name):
  (+m, (+k, (e, (ws, sn)))) = rp
  (m, (k, (Equal.trans(String, name, String.append("x-", r), String.append("x-", String.append(m, AwsText.sp_rid_tail(k))), v, Equal.cong(String, String, z => String.append("x-", z), r, String.append(m, AwsText.sp_rid_tail(k)), e)), LB.awb.wds_of(m, ws, sn))))

def aws.rp(+r: String, h: {A.rid.go(r, False{}) == True{} : Bool}) -> LB.awb.RidP(r, False{}, True{}):
  %h : LB.awb.RidP(r, False{}, _)
  LB.awb.rid_sp(r, False{})

def aws.m(-name: String, m: Maybe<&2, String>, v: LA.mnb.SP("x-", name, m), h: {A.rid.on(m) == True{} : Bool}) -> aws.G(name):
  match m:
    case None{}:
      LA.mnb.absurd_f(aws.G(name), h)
    case Some{+r}:
      aws.fin(name, r, v, aws.rp(r, h))

def AwsText.aws_rid_sound(name, h):
  aws.m(name, M.strip("x-", name), LA.mnb.sp("x-", name), h)
