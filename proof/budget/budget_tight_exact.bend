# eukhe: the proof of LAW budget_tight_exact
#
# PROOF: the grant's tight is the code's lack of the granted ask against
# what it left free, from when it ends (br.res_is), and a lack is exactly
# not fitting (br.tight_fits).

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ../../spec/budget/ledger.bend as S
import ./base/reserve.bend as BR

def Budget.budget_tight_exact(use, p, id, now, base, keep, want, less, a, i, c, a2, t, g):
  BR.br.tight(use, id, now, base, keep, want, less, a, i, c, a2, t, BR.br.res_is(use, p, id, now, base, keep, want, less, a, B.Granted{i, c, a2, t}, g))
