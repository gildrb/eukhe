# eukhe: the proof of LAW budget_grant_on_time
#
# PROOF: the granted ask fits (br.res_is), and fitting includes ending on
# time with the reserves' durations (br.on_time_of); the account answered
# keeps the deadline.

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ../../spec/budget/ledger.bend as S
import ./base/reserve.bend as BR

def Budget.budget_grant_on_time(use, p, id, now, base, keep, want, less, a, i, c, a2, t, g):
  BR.br.in_time(use, p, id, now, base, keep, want, less, a, i, c, a2, t, BR.br.res_is(use, p, id, now, base, keep, want, less, a, B.Granted{i, c, a2, t}, g))
