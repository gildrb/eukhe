# eukhe: the proof of LAW loop_restart_resumes_submit
#
# PROOF: lb.tied: every step leaves an act and a state that agree (lb.TiedTo:
# a state left by Submit{k, t} is in turn k with prompt t, so its restart is
# Resume{k, t}), by cases on the event and the flags the code tests; the
# premise rewrites the act to Submit{k, t} (lb.tied_submit).

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_restart_resumes_submit(s, e, k, t, h):
  LALoopBounds.lb.tied_submit(S.does(s, e), S.next(s, e), k, t, LALoopBounds.lb.tied(s, e), h)
