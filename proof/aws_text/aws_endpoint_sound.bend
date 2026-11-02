# eukhe: the proof of LAW aws_endpoint_sound

import Base
import ../../bend/model_name.bend as M
import ../../bend/aws_text.bend as A
import ../../laws/aws_text.bend as AwsText
import ../model_name/base.bend as LA
import ./base/region.bend as LR

def AwsText.aws_endpoint_sound(host, r, h):
  %h : LR.awr.EP(host, _)
  LR.awr.ep_after(host, M.strip("bedrock-runtime", host), LA.mnb.sp("bedrock-runtime", host))
