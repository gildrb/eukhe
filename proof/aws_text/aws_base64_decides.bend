# eukhe: the proof of LAW aws_base64_decides

import Base
import ../../bend/aws_text.bend as A
import ../../laws/aws_text.bend as AwsText
import ./base/b64.bend as LQ

def AwsText.aws_base64_decides(cs):
  LQ.awq.decides(cs)
