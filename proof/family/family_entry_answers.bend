# eukhe: the proof of LAW family_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left (fe.req_rt), so the entry answers the model's decision, which is the spec's (family_refusal_precedence, family_text_spec; fe.reply).

import Base
import ../../bend/family.bend as F
import ../../bend/ffi_family.bend as FF
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/family.bend as Family
import ./base/entry.bend as LE


def Family.family_entry_answers(q, fit):
  %Equal.sym(Wr.Dec<FF.Req>, FF.get_req(Family.fam_w_req(q, "")), Wr.Got{q, ""}, LE.fe.req_rt(q, "", fit)) : {FF.ffi.got(_) == Family.fam_w_reply(q) : String}
  LE.fe.reply(q)
