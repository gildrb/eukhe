# eukhe: the proof of LAW budget_settle_conserves
#
# PROOF: an id not held: nothing changes. A held id: what is held is the hold
# of the id plus the others' (induction on the holds); free and that hold,
# less the spend, plus the spend is free and the hold plus the spend past
# them (both are the larger of the two), and that excess is what the
# overrun grows by.

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ./base/settle.bend as BS

def Budget.budget_settle_conserves(id, act, a, d):
  match a:
    case B.Acct{f, s, l, o, hs, u}:
      BS.bs.conserve_if(B.held(id, hs), id, act, f, s, l, o, hs, u, d)
