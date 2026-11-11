# eukhe: the proof of LAW budget_carve_iff
#
# PROOF: an agent that is not Working is kept. A Working agent's carve is
# carved exactly when no dimension lacks: each of the code's five tests
# (want + base within free in each spent dimension, now + want's and base's
# durations by the deadline) is the spec's test with a final answer's
# reserve of nothing added (x + 0 = x).

import Base
import ../../laws/budget.bend as Budget
import ./base/tree.bend as BT

def Budget.budget_carve_iff(ph, now, want, base, a):
  BT.bt.carve_iff(ph, now, want, base, a)
