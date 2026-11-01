# eukhe: the proof of LAW aws_arn_complete
#
# PROOF: the fixed parts strip off as they are spelled; the partition
# suffix and the region are whole runs of region chars (awr.part_arn,
# awr.region_arn).

import Base
import ../../bend/aws_text.bend as A
import ../../laws/aws_text.bend as AwsText
import ./base/region.bend as LR

def AwsText.aws_arn_complete(a, r, rest, ha, hr):
  match a:
    case None{}:
      LR.awr.region_arn(r, rest, hr)
    case Some{x}:
      LR.awr.part_arn(x, r, rest, ha, hr)
