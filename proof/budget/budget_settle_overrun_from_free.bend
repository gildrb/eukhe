# eukhe: the proof of LAW budget_settle_overrun_from_free
#
# PROOF: a held id is found by the code's walk; what the code adds up under
# the id is what it holds (induction on the holds), so free becomes free
# and the hold less the spend and the overrun grows by the spend past them,
# in each dimension.

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ./base/settle.bend as BS

def Budget.budget_settle_overrun_from_free(id, act, a, d, open):
  match a:
    case B.Acct{f, s, l, o, hs, u}:
      BS.bs.from_free(id, act, f, s, l, o, hs, u, d, open)
