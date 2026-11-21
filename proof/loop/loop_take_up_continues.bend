# eukhe: the proof of LAW loop_take_up_continues
#
# PROOF: the restart of a loop in its turn computes to the same state, so
# each settle after it is the settle of the turn itself, the loop's own
# (lb.turn_mine). With no condition, no count and no deadline, a turn that
# ran computes to the next turn; a failed one does too once
# Lp.tired(1 + f) is replaced by False, from f < 2 (lb.errored_fresh).

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_take_up_continues(i, b, f, x, now, hf):
  +j = i
  (%LALoopBounds.lb.turn_mine(j, None{}, None{}, Lp.NoCond{}, b, f, x, Lp.Ran{}, False{}, now, True{}) : {_ == (Lp.St{Lp.Turn{}, 1n+i, None{}, None{}, Lp.NoCond{}, b, 0n, x}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act}; {==},
   %LALoopBounds.lb.errored_fresh(j, f, None{}, None{}, b, x, now, True{}, hf) : {_ == (Lp.St{Lp.Turn{}, 1n+i, None{}, None{}, Lp.NoCond{}, b, 1n+f, x}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act}; {==})
