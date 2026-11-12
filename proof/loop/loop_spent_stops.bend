# eukhe: the proof of LAW loop_spent_stops
#
# PROOF: both steps are rewritten to the advance past the failure cap
# (lb.go_fresh, lb.ran); funded and with Some{0n} left, Lp.spent computes to
# True, the halt to out-of-turns and the advance to that report and end.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_spent_stops(i, d, c, b, f, x, ev, now, hg, hf):
  +j = i
  (%LALoopBounds.lb.go_fresh(c, ev, j, f, Some{0n}, d, b, x, now, True{}, hg, hf) : {(S.act(_), S.phase(S.state(_))) == (Lp.Report{Lp.OutOfTurns{}}, Lp.Ended{Lp.OutOfTurns{}}) : Lp.Act & Lp.Phase}; {==},
   %LALoopBounds.lb.ran(j, Some{0n}, d, b, f, x, now, True{}) : {(S.act(_), S.phase(S.state(_))) == (Lp.Report{Lp.OutOfTurns{}}, Lp.Ended{Lp.OutOfTurns{}}) : Lp.Act & Lp.Phase}; {==})
