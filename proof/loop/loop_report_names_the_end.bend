# eukhe: the proof of LAW loop_report_names_the_end
#
# PROOF: lb.tied: every step leaves an act and a state that agree (lb.TiedTo:
# a state left by Report{w} is ended with w: `/loop` or a stop of a loop that
# is on, a halted advance, a confirmed or broken check), by cases on the
# event and the flags the code tests; the premise rewrites the act to
# Report{w} (lb.tied_report).

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_report_names_the_end(s, e, w, h):
  LALoopBounds.lb.tied_report(S.does(s, e), S.next(s, e), w, LALoopBounds.lb.tied(s, e), h)
