# eukhe: the proof of LAW budget_carve_kept_short
#
# PROOF: a Working agent's carve is kept short only for the dimension the
# code's lack names, and the code's lack names a dimension whose spec test
# fails (budget_refuse_short's lemma of reserve.bend), so the spec calls
# that dimension short.

import Base
import ../../laws/budget.bend as Budget
import ./base/tree.bend as BT

def Budget.budget_carve_kept_short(now, want, base, a, d, g):
  BT.bt.kept_short(now, want, base, a, d, g)
