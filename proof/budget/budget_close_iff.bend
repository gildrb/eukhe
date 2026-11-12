# eukhe: the proof of LAW budget_close_iff
#
# PROOF: the code closes exactly when the child has no hold and nothing
# lent in each spent dimension, which is the spec's idle test term by term.

import Base
import ../../laws/budget.bend as Budget
import ./base/tree.bend as BT

def Budget.budget_close_iff(c, p):
  BT.bt.close_iff(c, p)
