# eukhe: the proof of LAW budget_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left (be.req_rt), so the entry answers the model's decision by its encoders, which are the spec's spellings (be.reply).

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ../../bend/ffi_budget.bend as FBg
import ../../bend/wire.bend as Wr
import ../../spec/budget/ledger.bend as S
import ./base/entry.bend as BE

def Budget.budget_entry_answers(q, fit):
  %Equal.sym(Wr.Dec<FBg.Req>, FBg.get_req(Budget.sp_w_req(q, "")), Wr.Got{q, ""}, BE.be.req_rt(q, "", fit)) : {FBg.ffi.got(_) == Budget.sp_w_reply(q) : String}
  BE.be.reply(q)
