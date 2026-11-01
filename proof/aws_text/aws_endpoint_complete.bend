# eukhe: the proof of LAW aws_endpoint_complete
#
# PROOF: the fixed parts strip off as they are spelled; the region is the
# whole run of region chars before `.amazonaws.com` (awr.region_ep).

import Base
import ../../bend/aws_text.bend as A
import ../../laws/aws_text.bend as AwsText
import ./base/region.bend as LR

def AwsText.aws_endpoint_complete(f, r, c, h):
  match f:
    case True{}:
      LR.awr.region_ep(r, c, h)
    case False{}:
      LR.awr.region_ep(r, c, h)
