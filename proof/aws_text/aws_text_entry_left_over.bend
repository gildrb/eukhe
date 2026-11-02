# eukhe: the proof of LAW aws_text_entry_left_over

import Base
import ../../bend/ffi_aws_text.bend as FA
import ../../bend/wire.bend as Wr
import ../../laws/aws_text.bend as AwsText
import ./base/entry.bend as LE

def AwsText.aws_text_entry_left_over(q, rest, h, more):
  %Equal.sym(Wr.Dec<FA.Req>, FA.get_req(AwsText.sp_w_req(q, rest)), Wr.Got{q, rest}, LE.awe.req_rt(q, rest, h)) : {FA.ffi.got(_) == Wr.err("aws_text: malformed request") : String}
  %Equal.sym(Bool, String.is_empty(rest), False{}, more) : {FA.ffi.done(q, _) == Wr.err("aws_text: malformed request") : String}
  {==}
