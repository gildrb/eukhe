# eukhe: the proof of LAW loop_deadline_bounds
#
# PROOF: the state is opened and its deadline rewritten to Some{d}; lb.deadline
# splits the event: a new `/loop` is refuted by the premise; a settled turn or
# a judged check reaches Lp.advance only under a halt that the late clock
# makes Some (lb.halt_late); every other act is no Submit by computation.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_deadline_bounds(s, e, d, hd, hp):
  match s:
    case Lp.St{p, i, l, dd, c, b, f, x}:
      %Equal.sym(Maybe<&2, Nat>, dd, Some{d}, hd) : LALoopBounds.lb.NoSub(Lp.step(Lp.St{p, i, l, _, c, b, f, x}, e))
      LALoopBounds.lb.deadline(e, p, i, l, d, c, b, f, x, hp)
