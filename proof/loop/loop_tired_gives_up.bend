# eukhe: the proof of LAW loop_tired_gives_up
#
# PROOF: both steps are rewritten to Lp.advance (lb.go: the evidence that
# shows "not yet" is Refuted; lb.errored: the failed turn of a loop with no
# condition counts one more); with 3 + k failed turns Lp.tired computes to
# True and the advance to the turns-failed report and end.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_tired_gives_up(i, l, d, c, b, k, x, ev, now, fu, hg):
  +j = i
  (%LALoopBounds.lb.go(c, ev, j, l, d, b, 3n+k, x, now, fu, hg) : {(S.act(_), S.phase(S.state(_))) == (Lp.Report{Lp.TurnsFailed{}}, Lp.Ended{Lp.TurnsFailed{}}) : Lp.Act & Lp.Phase}; {==},
   %LALoopBounds.lb.errored(j, l, d, b, 2n+k, x, now, fu) : {(S.act(_), S.phase(S.state(_))) == (Lp.Report{Lp.TurnsFailed{}}, Lp.Ended{Lp.TurnsFailed{}}) : Lp.Act & Lp.Phase}; {==})
