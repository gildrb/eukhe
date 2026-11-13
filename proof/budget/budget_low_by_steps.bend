# eukhe: the proof of LAW budget_low_by_steps
#
# PROOF: the grant's low is the code's lack of two steps against what was
# free before the grant, from now (br.res_is); a lack is exactly not
# fitting, and the code's sum of two steps is the spec's (br.low_step).

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ../../spec/budget/ledger.bend as S
import ./base/reserve.bend as BR

def Budget.budget_low_by_steps(use, p, id, now, base, keep, step, want, less, a, i, c, a2, lo, g):
  BR.br.low(use, p, id, now, base, keep, step, want, less, a, i, c, a2, lo, BR.br.res_is(use, p, id, now, base, keep, step, want, less, a, B.Granted{i, c, a2, lo}, g))
