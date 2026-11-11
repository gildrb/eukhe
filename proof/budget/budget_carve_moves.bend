# eukhe: the proof of LAW budget_carve_moves
#
# PROOF: a carve answers Carved only for a Working agent whose free lacks
# nothing of the allotment with the reserves above by the deadline; then,
# in each spent dimension, want + base <= free, so (free - want) + want =
# free and base <= free - want; lent grows by want, the child holds want
# until now + want's duration, now + (want's + base's durations) <= the
# deadline, and the other fields are the account's (bt.moves).

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ../../spec/budget/ledger.bend as S
import ./base/tree.bend as BT

def Budget.budget_carve_moves(ph, now, want, base, a, p, c, d, g):
  %g : BT.bt.Moves(now, want, base, a, d, _)
  BT.bt.moves(ph, now, want, base, a, d)
