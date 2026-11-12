# eukhe: the proof of LAW budget_close_takes_overrun
#
# PROOF: a close answers Closed only for an idle child; then, in each
# dimension, the parent's free is its free and the child's less the child's
# overrun, the parent's overrun grows by the child's overrun past them, its
# spent by the child's spent; its holds and deadline stay and the child is
# empty (bt.takes).

import Base
import ../../laws/budget.bend as Budget
import ../../spec/budget/ledger.bend as S
import ./base/tree.bend as BT

def Budget.budget_close_takes_overrun(c, p, p2, c2, d, g):
  %g : BT.bt.Takes(p, S.free(c), S.spent(c), S.over(c), d, _)
  BT.bt.takes(c, p, d)
