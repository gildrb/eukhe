# eukhe: the proof of LAW budget_low_by_spend
#
# PROOF: each grant's low is exactly that two steps do not fit what was
# free before it (br.low, as in budget_low_by_steps), which names neither
# the offers nor the offer granted; so both are the same.

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ../../spec/budget/ledger.bend as S
import ./base/reserve.bend as BR

def Budget.budget_low_by_spend(use, p, id, now, base, keep, step, want, less, want2, less2, a, i, c, a2, lo, i2, c2, a3, lo2, g, g2):
  Equal.trans(Bool, lo, Bool.not(S.fits(use, base, keep, S.plus(step, step), S.free(a), now, S.until(a))), lo2,
    BR.br.low(use, p, id, now, base, keep, step, want, less, a, i, c, a2, lo, BR.br.res_is(use, p, id, now, base, keep, step, want, less, a, B.Granted{i, c, a2, lo}, g)),
    Equal.sym(Bool, lo2, Bool.not(S.fits(use, base, keep, S.plus(step, step), S.free(a), now, S.until(a))), BR.br.low(use, p, id, now, base, keep, step, want2, less2, a, i2, c2, a3, lo2, BR.br.res_is(use, p, id, now, base, keep, step, want2, less2, a, B.Granted{i2, c2, a3, lo2}, g2))))
