# eukhe: the proof of LAW budget_carve_kept_why
#
# PROOF: a carve by an agent in WrapUp or Exhausted computes to Kept as
# stopped. A Working agent's carve is carved exactly when its ask fits
# (budget_carve_iff's lemma), and otherwise it is kept for the dimension
# that lacks, so it fits or is kept short.

import Base
import ../../laws/budget.bend as Budget
import ./base/tree.bend as BT

def Budget.budget_carve_kept_why(now, want, base, a):
  ({==}, ({==}, BT.bt.kept_why(now, want, base, a)))
