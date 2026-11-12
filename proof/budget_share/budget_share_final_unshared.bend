# eukhe: the proof of LAW budget_share_final_unshared
#
# PROOF: a final answer is within the share whatever n is, so the first
# scan's test is the fit (bsm.ok_plain) and it finds the first offer that
# fits (bsm.ff).

import Base
import ../../bend/budget.bend as B
import ../../bend/budget_share.bend as Bs
import ../../spec/budget/ledger.bend as S
import ../../laws/budget_share.bend as BudgetShare
import ./base/model.bend as BSM

def BudgetShare.budget_share_final_unshared(n, base, keep, want, less, free, now, until, some):
  BSM.bsm.ff(Bs.first(want <> less, n, B.Final{}, base, keep, free, now, until), Bs.last(want <> less, B.Final{}, base, keep, free, now, until), n, B.Final{}, base, keep, free, now, until, want <> less, BSM.bsm.first_ok(want <> less, n, B.Final{}, base, keep, free, now, until), {==}, some)
