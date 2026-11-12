# eukhe: the proof of LAW budget_close_returns
#
# PROOF: a close answers Closed only for an idle child; then, in a
# dimension where the child has no overrun, nothing is taken from free or
# added to the parent's overrun, so the parent's free grows by the child's
# free, its spent by the child's spent, and lent shrinks by both; the
# parent's holds and deadline stay and the child is empty (bt.returns).

import Base
import ../../laws/budget.bend as Budget
import ../../spec/budget/ledger.bend as S
import ./base/tree.bend as BT

def Budget.budget_close_returns(c, p, p2, c2, d, g, clean):
  %g : BT.bt.Returns(p, S.free(c), S.spent(c), d, _)
  BT.bt.returns(c, p, d, clean)
