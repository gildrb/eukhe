# eukhe: the proof of LAW aws_fips_first

import Base
import ../../bend/aws_text.bend as A
import ../../laws/aws_text.bend as AwsText
import ./base/fips.bend as LF

def AwsText.aws_fips_first(a, k, r, ha, hk):
  LF.awf.first(a, k, r, ha, hk)
