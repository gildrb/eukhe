# eukhe: the proof of LAW budget_grant_within
#
# PROOF: the answer of a reservation says what it granted (br.res_is): the
# granted ask fits what was free with the reserves, so in each dimension d
# it is within free, and what the grant left (free less the amount) and
# the amount add up to free (br.left).

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ../../spec/budget/ledger.bend as S
import ./base/reserve.bend as BR

def Budget.budget_grant_within(use, p, id, now, base, keep, step, want, less, a, i, c, a2, lo, d, g):
  BR.br.within(use, p, id, now, base, keep, step, want, less, a, i, c, a2, lo, d, BR.br.res_is(use, p, id, now, base, keep, step, want, less, a, B.Granted{i, c, a2, lo}, g))
