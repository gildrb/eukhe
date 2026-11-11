# eukhe: the proof of LAW budget_settle_charges
#
# PROOF: a held id is found by the code's walk, so the settlement adds the
# spend to spent, keeps only the holds of the other ids (which do not hold
# the id, induction on the holds), lent and the deadline.

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ./base/settle.bend as BS

def Budget.budget_settle_charges(id, act, a, d, open):
  match a:
    case B.Acct{f, s, l, o, hs, u}:
      BS.bs.charges(id, act, f, s, l, o, hs, u, d, open)
