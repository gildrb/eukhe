# eukhe: the proof of LAW loop_unfunded_never_starts
#
# PROOF: lb.unfunded splits the event under the premise (lb.When): only a
# settled turn or a judged check with funded False remains, and there every
# advance runs under a halt that is Some (lb.halt_unfunded: turns-failed or
# out-of-budget), so no act is a Submit (lb.ns_settled, lb.ns_judged).

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_unfunded_never_starts(s, e, h):
  match s:
    case Lp.St{p, i, l, d, c, b, f, x}:
      LALoopBounds.lb.when(S.unfunded(e), LALoopBounds.lb.NoSub(Lp.step(Lp.St{p, i, l, d, c, b, f, x}, e)), h, LALoopBounds.lb.unfunded(e, p, i, l, d, c, b, f, x))
