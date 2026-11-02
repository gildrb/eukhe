# eukhe: the proof of LAW aws_rid_decides

import Base
import ../../bend/aws_text.bend as A
import ../../laws/aws_text.bend as AwsText
import ./base.bend as LB

def AwsText.aws_rid_decides(names):
  LB.awb.rid_index(names, 0n)
