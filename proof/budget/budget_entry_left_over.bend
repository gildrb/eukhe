# eukhe: the proof of LAW budget_entry_left_over
#
# PROOF: the spelled request reads back with the rest untouched (be.req_rt); the rest is not empty, so the entry answers the error form.

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ../../bend/ffi_budget.bend as FBg
import ../../bend/wire.bend as Wr
import ../../spec/budget/ledger.bend as S
import ./base/entry.bend as BE

def Budget.budget_entry_left_over(q, ch, t, fit):
  %Equal.sym(Wr.Dec<FBg.Req>, FBg.get_req(Budget.sp_w_req(q, SCon{ch, t})), Wr.Got{q, SCon{ch, t}}, BE.be.req_rt(q, SCon{ch, t}, fit)) : {FBg.ffi.got(_) == Wr.err("budget: malformed request") : String}
  {==}
