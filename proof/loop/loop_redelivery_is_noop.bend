# eukhe: the proof of LAW loop_redelivery_is_noop
#
# PROOF: lb.noop splits the event under the premise (lb.When). A stop or an
# abort: by the phase. A settled turn or a judged check that is not the
# loop's own changed nothing and is not its own again; its own moved the
# loop to a phase or an iteration (1 + i, lb.eq_not_succ) where it is stale;
# a cancelled check changed nothing and does the same again.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_redelivery_is_noop(s, e, h):
  match s:
    case Lp.St{p, i, l, d, c, b, f, x}:
      LALoopBounds.lb.when(S.once(e), LALoopBounds.lb.Noop(Lp.step(Lp.St{p, i, l, d, c, b, f, x}, e), e), h, LALoopBounds.lb.noop(e, p, i, l, d, c, b, f, x))
