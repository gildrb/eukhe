# eukhe: the proof of LAW redirect_input_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left (rie.req_rt), so the entry answers the model's answer, spelled by encoders that are the laws' spellers (rie.answer).

import Base
import ../../bend/redirect_input.bend as Ri
import ../../bend/ffi_redirect_input.bend as FRi
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/redirect_input.bend as RedirectInput
import ./base/entry.bend as LE

def ria.reply(q: FRi.Req) -> {FRi.answer(q) == RedirectInput.ri_w_reply(q) : String}:
  match q:
    case FRi.QClean{x}:
      {==}
    case FRi.QParse{x}:
      LE.rie.answer(Ri.parse(x))
    case FRi.QVerify{c, m, e}:
      LE.rie.answer(Ri.verify(c, m, e))
    case FRi.QText{f}:
      {==}
    case FRi.QNotice{x}:
      {==}

def RedirectInput.redirect_input_entry_answers(q, fit):
  %Equal.sym(Wr.Dec<FRi.Req>, FRi.get_req(RedirectInput.ri_w_req(q, "")), Wr.Got{q, ""}, LE.rie.req_rt(q, "", fit)) : {FRi.ffi.got(_) == RedirectInput.ri_w_reply(q) : String}
  ria.reply(q)
