# eukhe: the proof of LAW loop_enter_sets_bounds
#
# PROOF: the state is opened; lb.enter_bounds splits the phase under the
# premise (lb.Unless): off or ended, `/loop` is Lp.start, whose state has
# Lp.turns and Lp.until of the limit with or without an inline prompt
# (lb.start_bounds); for a count, a span and no limit these compute to the
# three claims.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_enter_sets_bounds(s, n, ms, c, pr, now, off):
  match s:
    case Lp.St{p, i, l, d, c0, b, f, x}:
      +q = pr
      +o = off
      (LALoopBounds.lb.enter_bounds(p, q, i, l, d, c0, b, f, x, Lp.Count{n}, c, now, o),
       LALoopBounds.lb.enter_bounds(p, q, i, l, d, c0, b, f, x, Lp.Span{ms}, c, now, o),
       LALoopBounds.lb.enter_bounds(p, q, i, l, d, c0, b, f, x, Lp.NoLimit{}, c, now, o))
