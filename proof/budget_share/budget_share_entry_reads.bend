# eukhe: the proof of LAW budget_share_entry_reads
#
# PROOF: field by field, each decoder reads its spelling back (bse.reads,
# from the budget entry's round trips be.nat, be.ask, be.asks, be.amt).

import Base
import ../../bend/budget.bend as B
import ../../bend/budget_share.bend as Bs
import ../../bend/ffi_budget_share.bend as FBs
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/budget_share.bend as BudgetShare
import ./base/entry.bend as BSE
def BudgetShare.budget_share_entry_reads(q, rest, fit):
  BSE.bse.reads(q, rest, fit)
