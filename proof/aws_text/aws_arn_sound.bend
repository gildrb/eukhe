# eukhe: the proof of LAW aws_arn_sound

import Base
import ../../bend/model_name.bend as M
import ../../bend/aws_text.bend as A
import ../../laws/aws_text.bend as AwsText
import ../model_name/base.bend as LA
import ./base/region.bend as LR

def AwsText.aws_arn_sound(id, r, h):
  %h : LR.awr.ARP(id, _)
  LR.awr.ar_after(id, M.strip("arn:aws", id), LA.mnb.sp("arn:aws", id))
