# eukhe: the proof of LAW budget_share_smallest_fit
#
# PROOF: none is within the share, so the first scan finds none
# (bsm.first_ok, bsm.no_mok) and the start is what the last scan finds,
# the last offer that fits (bsm.last_ok); some fits, so it finds one
# (bsm.sf).

import Base
import ../../bend/budget.bend as B
import ../../bend/budget_share.bend as Bs
import ../../spec/budget/ledger.bend as S
import ../../laws/budget_share.bend as BudgetShare
import ./base/model.bend as BSM

def BudgetShare.budget_share_smallest_fit(n, use, base, keep, want, less, free, now, until, none, some):
  BSM.bsm.sf(Bs.first(want <> less, n, use, base, keep, free, now, until), Bs.last(want <> less, use, base, keep, free, now, until), n, use, base, keep, free, now, until, want <> less, BSM.bsm.first_ok(want <> less, n, use, base, keep, free, now, until), BSM.bsm.last_ok(want <> less, use, base, keep, free, now, until), none, some)
