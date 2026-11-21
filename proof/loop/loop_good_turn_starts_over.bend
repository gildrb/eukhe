# eukhe: the proof of LAW loop_good_turn_starts_over
#
# PROOF: both events are the loop's own (lb.turn_mine: Nat.is_eq(i, i) is
# True), so each step is Lp.settled.mine of the turn that ran, which is
# the gate with 0 failed turns whatever the count before it.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_good_turn_starts_over(i, l, d, c, b, f, x, now, fu):
  %LALoopBounds.lb.turn_mine(i, l, d, c, b, f, x, Lp.Ran{}, False{}, now, fu) : {_ == Lp.step(Lp.St{Lp.Turn{}, i, l, d, c, b, 0n, x}, Lp.Settled{i, Lp.Ran{}, False{}, now, fu}) : Lp.St & Lp.Act}
  %LALoopBounds.lb.turn_mine(i, l, d, c, b, 0n, x, Lp.Ran{}, False{}, now, fu) : {Lp.settled.mine(False{}, Lp.Ran{}, i, l, d, c, b, f, x, now, fu) == _ : Lp.St & Lp.Act}
  {==}
