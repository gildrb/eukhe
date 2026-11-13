# eukhe: the proof of LAW budget_share_none_fits_first
#
# PROOF: an offer either scan finds fits (bsm.first_ok, bsm.last_ok,
# bsm.mok_mfits), and none does (bsm.no_mfits): both find none and the
# start is 0 (bsm.nf0).

import Base
import ../../bend/budget.bend as B
import ../../bend/budget_share.bend as Bs
import ../../spec/budget/ledger.bend as S
import ../../laws/budget_share.bend as BudgetShare
import ./base/model.bend as BSM

def BudgetShare.budget_share_none_fits_first(n, use, base, keep, want, less, free, now, until, none):
  BSM.bsm.nf0(Bs.first(want <> less, n, use, base, keep, free, now, until), Bs.last(want <> less, use, base, keep, free, now, until), n, use, base, keep, free, now, until, want <> less, BSM.bsm.first_ok(want <> less, n, use, base, keep, free, now, until), BSM.bsm.last_ok(want <> less, use, base, keep, free, now, until), none)
