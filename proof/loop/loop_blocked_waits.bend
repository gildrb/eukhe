# eukhe: the proof of LAW loop_blocked_waits
#
# PROOF: lb.blocked splits the event under the premise (lb.When): only a
# settled turn or a judged check with blocked True remains; by the phase and
# the Bool `Nat.is_eq(k, i)`, the step either ignores the event (Rest) or
# defers it (Defer), and rebuilds the same state both ways.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_blocked_waits(s, e, h):
  match s:
    case Lp.St{p, i, l, d, c, b, f, x}:
      LALoopBounds.lb.when(S.blocked(e), LALoopBounds.lb.Waits(Lp.step(Lp.St{p, i, l, d, c, b, f, x}, e), Lp.St{p, i, l, d, c, b, f, x}), h, LALoopBounds.lb.blocked(e, p, i, l, d, c, b, f, x))
