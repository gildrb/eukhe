# eukhe: the proof of LAW loop_unfunded_stops
#
# PROOF: both steps are rewritten to the advance past the failure cap
# (lb.go_fresh: "not yet" is Refuted and fewer than three failed turns are not
# tired; lb.ran: a turn that ran has 0 failed turns); with funded False the
# halt computes to out-of-budget, the advance to that report and end.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_unfunded_stops(i, l, d, c, b, f, x, ev, now, hg, hf):
  +j = i
  (%LALoopBounds.lb.go_fresh(c, ev, j, f, l, d, b, x, now, False{}, hg, hf) : {(S.act(_), S.phase(S.state(_))) == (Lp.Report{Lp.OutOfBudget{}}, Lp.Ended{Lp.OutOfBudget{}}) : Lp.Act & Lp.Phase}; {==},
   %LALoopBounds.lb.ran(j, l, d, b, f, x, now, False{}) : {(S.act(_), S.phase(S.state(_))) == (Lp.Report{Lp.OutOfBudget{}}, Lp.Ended{Lp.OutOfBudget{}}) : Lp.Act & Lp.Phase}; {==})
