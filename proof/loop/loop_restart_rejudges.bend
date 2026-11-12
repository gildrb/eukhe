# eukhe: the proof of LAW loop_restart_rejudges
#
# PROOF: lb.tied: every step leaves an act and a state that agree (lb.TiedTo:
# a state left by Judge{k} is judging iteration k, so its restart is
# Judge{k}), by cases on the event and the flags the code tests; the premise
# rewrites the act to Judge{k} (lb.tied_judge).

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_restart_rejudges(s, e, k, h):
  LALoopBounds.lb.tied_judge(S.does(s, e), S.next(s, e), k, LALoopBounds.lb.tied(s, e), h)
