# eukhe: the proof of LAW budget_share_lone_is_first_fit
#
# PROOF: alone, an offer that fits is within the share (what is free past
# the reserves divided by 1: bsm.within_plain, bsa.div_one), so the first
# scan's test is the fit (bsm.ok_plain) and it finds the first offer that
# fits (bsm.ff).

import Base
import ../../bend/budget.bend as B
import ../../bend/budget_share.bend as Bs
import ../../spec/budget/ledger.bend as S
import ../../laws/budget_share.bend as BudgetShare
import ./base/model.bend as BSM

def BudgetShare.budget_share_lone_is_first_fit(use, base, keep, want, less, free, now, until, some):
  BSM.bsm.ff(Bs.first(want <> less, 1n, use, base, keep, free, now, until), Bs.last(want <> less, use, base, keep, free, now, until), 1n, use, base, keep, free, now, until, want <> less, BSM.bsm.first_ok(want <> less, 1n, use, base, keep, free, now, until), BSM.bsm.plain_one(use), some)
