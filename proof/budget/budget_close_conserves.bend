# eukhe: the proof of LAW budget_close_conserves
#
# PROOF: in one dimension the parent's free becomes (pf + cf) - co, spent
# ps + cs, lent pl - ((cf + cs) - co), the overrun po + (co - (pf + cf)).
# With co <= cf + cs and (cf + cs) - co <= pl, adding co to both sides and
# using that (x - y) + y and x + (y - x) are both the larger of x and y
# gives the conservation (bt.conserves).

import Base
import ../../laws/budget.bend as Budget
import ./base/tree.bend as BT

def Budget.budget_close_conserves(c, p, p2, c2, d, g, funded, ours):
  %g : BT.bt.Conserves(p, d, _)
  BT.bt.conserves(c, p, d, funded, ours)
