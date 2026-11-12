# eukhe: the proof of LAW budget_fund_repays_first
#
# PROOF: funding x on the overrun o leaves o - x overrun and adds x - o to
# free, in each dimension.

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ./base/settle.bend as BS

def Budget.budget_fund_repays_first(n, a, d):
  match n a:
    case B.Ask{+x, m} B.Acct{f, s, l, +o, hs, u}:
      (BS.bs.at_sub4(d, o, x), BS.bs.repays(x, f, o, d))
