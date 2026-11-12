# eukhe: the proof of LAW budget_share_first_within
#
# PROOF: the first scan finds the first offer that fits and is within the
# share (bsm.first_ok); some is, so the scan finds one and the start is its
# place (bsm.fw).

import Base
import ../../bend/budget.bend as B
import ../../bend/budget_share.bend as Bs
import ../../spec/budget/ledger.bend as S
import ../../laws/budget_share.bend as BudgetShare
import ./base/model.bend as BSM

def BudgetShare.budget_share_first_within(n, use, base, keep, want, less, free, now, until, some):
  BSM.bsm.fw(Bs.first(want <> less, n, use, base, keep, free, now, until), Bs.last(want <> less, use, base, keep, free, now, until), n, use, base, keep, free, now, until, want <> less, BSM.bsm.first_ok(want <> less, n, use, base, keep, free, now, until), some)
