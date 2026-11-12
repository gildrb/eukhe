# eukhe: the proof of LAW loop_enter_starts_fresh
#
# PROOF: the state is opened; lb.enter_fresh splits the phase under the
# premise (lb.Unless): off or ended, `/loop` is Lp.start, which builds its
# state from the limit, the condition and the prompt alone: iteration 1
# with an inline prompt and 0 without, 0 failed turns, NoCheck; in every
# other phase the premise is False.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_enter_starts_fresh(s, lim, c, t, now, off):
  match s:
    case Lp.St{p, i, l, d, c0, b, f, x}:
      LALoopBounds.lb.enter_fresh(p, i, l, d, c0, b, f, x, lim, c, t, now, off)
