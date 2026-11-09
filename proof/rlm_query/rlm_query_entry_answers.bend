# eukhe: the proof of LAW rlm_query_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left (re.req_rt), so the entry answers the model's decision, which is the spec's (qp.plan, qc.code, qc.spec, re.text; re.reply).

import Base
import ../../bend/ffi_rlm_query.bend as FRq
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/rlm_query.bend as RlmQuery
import ./base/entry.bend as LE


def RlmQuery.rlm_query_entry_answers(q, fit):
  %Equal.sym(Wr.Dec<FRq.Req>, FRq.get_req(RlmQuery.rq_w_req(q, "")), Wr.Got{q, ""}, LE.re.req_rt(q, "", fit)) : {FRq.ffi.got(_) == RlmQuery.rq_w_reply(q) : String}
  LE.re.reply(q)
