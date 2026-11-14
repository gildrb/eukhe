# eukhe: the proof of LAW loop_end_keeps_iteration
#
# PROOF: lb.ends: every step that reports an end leaves the state at the
# iteration it started from (lb.EndAt: `/loop` or a stop of a loop that is
# on, a halted advance, a confirmed or broken check all rebuild the state
# with the same iteration), by cases on the event and the flags the code
# tests; the premise rewrites the act to Report{w} (lb.ends_report).

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_end_keeps_iteration(s, e, w, h):
  LALoopBounds.lb.ends_report(S.does(s, e), S.next(s, e), S.iter(s), w, LALoopBounds.lb.ends(s, e), h)
