# eukhe: the proof of LAW loop_halted_turn_pauses
#
# PROOF: the event is the loop's own (lb.turn_mine: Nat.is_eq(i, i) is True);
# the step of a halted turn in an idle session then computes to the pause.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_halted_turn_pauses(i, l, d, c, b, f, x, now, fu):
  %LALoopBounds.lb.turn_mine(i, l, d, c, b, f, x, Lp.Halted{}, False{}, now, fu) : {(S.act(_), S.phase(S.state(_))) == (Lp.Rest{}, Lp.Paused{}) : Lp.Act & Lp.Phase}
  {==}
