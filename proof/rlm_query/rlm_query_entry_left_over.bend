# eukhe: the proof of LAW rlm_query_entry_left_over
#
# PROOF: the spelled request reads back with the rest untouched (re.req_rt); the rest is not empty, so the entry answers the error form.

import Base
import ../../bend/ffi_rlm_query.bend as FRq
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/rlm_query.bend as RlmQuery
import ./base/entry.bend as LE


def RlmQuery.rlm_query_entry_left_over(q, ch, t, fit):
  %Equal.sym(Wr.Dec<FRq.Req>, FRq.get_req(RlmQuery.rq_w_req(q, SCon{ch, t})), Wr.Got{q, SCon{ch, t}}, LE.re.req_rt(q, SCon{ch, t}, fit)) : {FRq.ffi.got(_) == Wr.err("rlm_query: malformed request") : String}
  {==}
