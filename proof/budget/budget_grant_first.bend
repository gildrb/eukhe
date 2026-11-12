# eukhe: the proof of LAW budget_grant_first
#
# PROOF: the grant is the pick among the offers (br.res_is), and the pick is
# the first offer that fits: by induction on the offers, the pick from
# the next place being the pick one place later (br.pick_ok).

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ../../spec/budget/ledger.bend as S
import ./base/reserve.bend as BR

def Budget.budget_grant_first(use, p, id, now, base, keep, want, less, a, i, c, a2, t, g):
  BR.br.first(use, id, now, base, keep, want, less, a, i, c, a2, t, BR.br.res_is(use, p, id, now, base, keep, want, less, a, B.Granted{i, c, a2, t}, g))
