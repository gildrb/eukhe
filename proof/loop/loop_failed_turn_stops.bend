# eukhe: the proof of LAW loop_failed_turn_stops
#
# PROOF: with f < 2 the failed turn is not the third in a row
# (lb.errored_fresh: the budget, the count and the time decide), and with
# the deadline reached the time is late (lb.errored_time); the step then
# computes to each bound's end.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_failed_turn_stops(i, l, d, n, dl, b, f, x, now, hf, hl):
  +j = i
  +q = hf
  +t = hl
  (%LALoopBounds.lb.errored_fresh(j, f, l, d, b, x, now, False{}, q) : {(S.act(_), S.phase(S.state(_))) == (Lp.Report{Lp.OutOfBudget{}}, Lp.Ended{Lp.OutOfBudget{}}) : Lp.Act & Lp.Phase}; {==},
   %LALoopBounds.lb.errored_fresh(j, f, Some{0n}, d, b, x, now, True{}, q) : {(S.act(_), S.phase(S.state(_))) == (Lp.Report{Lp.OutOfTurns{}}, Lp.Ended{Lp.OutOfTurns{}}) : Lp.Act & Lp.Phase}; {==},
   %LALoopBounds.lb.errored_time(True{}, j, f, Some{1n+n}, dl, b, x, now, True{}, q, t) : {(S.act(_), S.phase(S.state(_))) == (Lp.Report{Lp.OutOfTime{}}, Lp.Ended{Lp.OutOfTime{}}) : Lp.Act & Lp.Phase}; {==},
   %LALoopBounds.lb.errored_time(True{}, j, f, None{}, dl, b, x, now, True{}, q, t) : {(S.act(_), S.phase(S.state(_))) == (Lp.Report{Lp.OutOfTime{}}, Lp.Ended{Lp.OutOfTime{}}) : Lp.Act & Lp.Phase}; {==})
