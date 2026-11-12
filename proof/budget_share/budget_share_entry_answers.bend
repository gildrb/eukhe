# eukhe: the proof of LAW budget_share_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left
# (bse.reads), so the entry answers the model's start spelled (bse.reply).

import Base
import ../../bend/budget.bend as B
import ../../bend/budget_share.bend as Bs
import ../../bend/ffi_budget_share.bend as FBs
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/budget_share.bend as BudgetShare
import ./base/entry.bend as BSE
def BudgetShare.budget_share_entry_answers(q, fit):
  %Equal.sym(Wr.Dec<FBs.Req>, FBs.get_req(BudgetShare.sh_w_req(q, "")), Wr.Got{q, ""}, BSE.bse.reads(q, "", fit)) : {FBs.ffi.got(_) == BudgetShare.sh_reply(q) : String}
  BSE.bse.reply(q)
