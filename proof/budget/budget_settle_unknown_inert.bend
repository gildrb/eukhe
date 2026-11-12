# eukhe: the proof of LAW budget_settle_unknown_inert
#
# PROOF: the code's walk of the holds finds an id exactly when the spec has
# it (induction on the holds); an id not found leaves the account as it was.

import Base
import ../../laws/budget.bend as Budget
import ./base/settle.bend as BS

def Budget.budget_settle_unknown_inert(id, act, a, miss):
  BS.bs.inert(id, act, a, miss)
