# eukhe: the proof of LAW loop_good_turn_forgives
#
# PROOF: the event is the loop's own (lb.turn_mine: Nat.is_eq(i, i) is True),
# so the step is the gate with 0 failed turns; lb.gate_fails: the gate keeps
# that count, with a condition (Judge) or without (either arm of the advance).

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_good_turn_forgives(i, l, d, c, b, f, x, now, fu):
  %LALoopBounds.lb.turn_mine(i, l, d, c, b, f, x, Lp.Ran{}, False{}, now, fu) : {S.fails(S.state(_)) == 0n : Nat}
  LALoopBounds.lb.gate_fails(c, i, l, d, b, 0n, x, now, fu)
