# eukhe: the proof of LAW budget_settle_within
#
# PROOF: a held id: free becomes free and the hold less the spend, the
# overrun grows by the spend past free and the hold. A spend within the
# hold is within free and the hold, so nothing is past them and what is
# left plus the spend is free and the hold.

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ./base/settle.bend as BS

def Budget.budget_settle_within(id, act, a, d, open, within):
  match a:
    case B.Acct{f, s, l, o, hs, u}:
      BS.bs.within(id, act, f, s, l, o, hs, u, d, open, within)
