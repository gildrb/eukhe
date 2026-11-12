# eukhe: the proof of LAW budget_carve_close_round_trip
#
# PROOF: a carved child holds the allotment w, has spent, lent and overrun
# nothing: it is idle. Its close gives the parent ((f - w) + w) - 0 = f
# free (w <= f in each spent dimension, since the carve fit), spent s + 0,
# lent (l + w) - ((w + 0) - 0) = l, the overrun o + (0 - x) = o, its holds
# and deadline; the child is empty (bt.round).

import Base
import ../../laws/budget.bend as Budget
import ./base/tree.bend as BT

def Budget.budget_carve_close_round_trip(ph, now, want, base, a, p, c, g):
  %g : BT.bt.Round(a, _)
  BT.bt.round(ph, now, want, base, a)
