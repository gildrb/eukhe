# eukhe: the proof of LAW aws_text_entry_decides
#
# PROOF: the spelled request reads back whole (awe.req_rt), nothing is left,
# and the answer is the spelled model answer (awe.answer).

import Base
import ../../bend/ffi_aws_text.bend as FA
import ../../bend/wire.bend as Wr
import ../../laws/aws_text.bend as AwsText
import ./base/entry.bend as LE

def AwsText.aws_text_entry_decides(q, h):
  %Equal.sym(Wr.Dec<FA.Req>, FA.get_req(AwsText.sp_w_req(q, "")), Wr.Got{q, ""}, LE.awe.req_rt(q, "", h)) : {FA.ffi.got(_) == AwsText.sp_w_reply(q) : String}
  LE.awe.answer(q)
