# eukhe: the proof of LAW loop_blocked_defers
#
# PROOF: each event is the loop's own (lb.turn_mine, lb.judging_mine:
# Nat.is_eq(i, i) is True); with blocked True the step computes to Defer.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_blocked_defers(i, l, d, c, b, f, x, o, ev, now, fu):
  +j = i
  (%LALoopBounds.lb.turn_mine(j, l, d, c, b, f, x, o, True{}, now, fu) : {S.act(_) == Lp.Defer{} : Lp.Act}; {==}, %LALoopBounds.lb.judging_mine(j, l, d, c, b, f, x, ev, True{}, now, fu) : {S.act(_) == Lp.Defer{} : Lp.Act}; {==})
