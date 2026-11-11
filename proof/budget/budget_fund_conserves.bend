# eukhe: the proof of LAW budget_fund_conserves
#
# PROOF: free grows by the amount past the overrun and the overrun shrinks
# to what is past the amount; the amount past the overrun plus the overrun
# is the amount plus the overrun past the amount (both are the larger of
# the two). The deadline grows by the duration; the other fields compute.

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ./base/settle.bend as BS

def Budget.budget_fund_conserves(n, a, d):
  match n a:
    case B.Ask{x, m} B.Acct{f, s, l, o, hs, u}:
      (BS.bs.fund_net(x, f, s, l, o, hs, u, Nat.add(u, m), d), ({==}, ({==}, ({==}, {==}))))
