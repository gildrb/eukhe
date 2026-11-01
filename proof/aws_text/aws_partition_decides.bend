# eukhe: the proof of LAW aws_partition_decides

import Base
import ../../bend/aws_text.bend as A
import ../../laws/aws_text.bend as AwsText
import ./base.bend as LB

def AwsText.aws_partition_decides(r):
  LB.awb.part_go(A.partitions(), r, 0n)
