# eukhe: the proof of LAW aws_shape_complete

import Base
import ../../bend/aws_text.bend as A
import ../../laws/aws_text.bend as AwsText
import ./base.bend as LB

def AwsText.aws_shape_complete(p, w, n, hw, hn):
  LB.awb.shape_app(p, w, n, hw, hn)
