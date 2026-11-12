# eukhe: the proof of LAW budget_grant_holds
#
# PROOF: the answer of a reservation says what it granted (br.res_is): the
# account answered is the old one with free reduced and the hold of the
# granted amount under the id put first; its other parts compute.

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ../../spec/budget/ledger.bend as S
import ./base/reserve.bend as BR

def Budget.budget_grant_holds(use, p, id, now, base, keep, want, less, a, i, c, a2, t, g):
  BR.br.holds(use, p, id, now, base, keep, want, less, a, i, c, a2, t, BR.br.res_is(use, p, id, now, base, keep, want, less, a, B.Granted{i, c, a2, t}, g))
