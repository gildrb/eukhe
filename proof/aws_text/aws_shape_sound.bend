# eukhe: the proof of LAW aws_shape_sound

import Base
import ../../bend/model_name.bend as M
import ../../bend/aws_text.bend as A
import ../../laws/aws_text.bend as AwsText
import ../model_name/base.bend as LA
import ./base.bend as LB

def AwsText.aws_shape_sound(p, r, h):
  LB.awb.ss_m(p, r, M.strip(String.append(p, "-"), r), LA.mnb.sp(String.append(p, "-"), r), h)
