# eukhe: the proof of LAW aws_rid_complete
#
# PROOF: `x-` strips off; M then a tail is accepted (awb.rid_app), M being
# one or more word chars or `-`.

import Base
import ../../bend/aws_text.bend as A
import ../../laws/aws_text.bend as AwsText
import ../model_name/base.bend as LA
import ./base.bend as LB

def awc.go(m: String, +k: Bool, h: {AwsText.sp_wds(m) == True{} : Bool}) -> {A.rid.go(String.append(m, AwsText.sp_rid_tail(k)), False{}) == True{} : Bool}:
  match m:
    case SNil{}:
      LA.mnb.absurd_f({A.rid.go(AwsText.sp_rid_tail(k), False{}) == True{} : Bool}, h)
    case SCon{x, +t}:
      LB.awb.rid_app(SCon{x, t}, k, False{}, h, {==})

def AwsText.aws_rid_complete(m, k, h):
  awc.go(m, k, h)
