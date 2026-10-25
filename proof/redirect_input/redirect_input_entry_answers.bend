# eukhe: the proof of LAW redirect_input_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left (rie.req_rt), so the entry answers the model's answer, the spec's (the model laws), spelled by encoders that are the spec spellers (rie.answer).

import Base
import ../../bend/redirect_input.bend as Ri
import ../../bend/ffi_redirect_input.bend as FRi
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/redirect_input.bend as RedirectInput
import ./base/entry.bend as LE
import ./redirect_input_clean_spec.bend as PRedirectInputCleanSpec
import ./redirect_input_parse_spec.bend as PRedirectInputParseSpec
import ./redirect_input_verify_spec.bend as PRedirectInputVerifySpec
import ./redirect_input_text_spec.bend as PRedirectInputTextSpec
import ./redirect_input_notice_spec.bend as PRedirectInputNoticeSpec

def ria.reply(q: FRi.Req) -> {FRi.answer(q) == RedirectInput.ri_w_reply(q) : String}:
  match q:
    case FRi.QClean{+x}:
      %RedirectInput.redirect_input_clean_spec(x) : {Wr.put_str(Ri.clean(x), "") == Wr.put_str(_, "") : String}
      {==}
    case FRi.QParse{+x}:
      %RedirectInput.redirect_input_parse_spec(x) : {FRi.put_answer(Ri.parse(x)) == RedirectInput.ri_w_answer(_) : String}
      LE.rie.answer(Ri.parse(x))
    case FRi.QVerify{+c, +m, +e}:
      %RedirectInput.redirect_input_verify_spec(c, m, e) : {FRi.put_answer(Ri.verify(c, m, e)) == RedirectInput.ri_w_answer(_) : String}
      LE.rie.answer(Ri.verify(c, m, e))
    case FRi.QText{+f}:
      %RedirectInput.redirect_input_text_spec(f) : {Wr.put_str(Ri.text(f), "") == Wr.put_str(_, "") : String}
      {==}
    case FRi.QNotice{+x}:
      %RedirectInput.redirect_input_notice_spec(x) : {Wr.put_str(Ri.notice(x), "") == Wr.put_str(_, "") : String}
      {==}

def RedirectInput.redirect_input_entry_answers(q, fit):
  %Equal.sym(Wr.Dec<FRi.Req>, FRi.get_req(RedirectInput.ri_w_req(q, "")), Wr.Got{q, ""}, LE.rie.req_rt(q, "", fit)) : {FRi.ffi.got(_) == RedirectInput.ri_w_reply(q) : String}
  ria.reply(q)
