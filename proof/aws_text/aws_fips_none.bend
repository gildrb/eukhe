# eukhe: the proof of LAW aws_fips_none

import Base
import ../../bend/aws_text.bend as A
import ../../laws/aws_text.bend as AwsText
import ./base/fips.bend as LF

def AwsText.aws_fips_none(s, h):
  LF.awf.none(s, h)
