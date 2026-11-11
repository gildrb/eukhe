# eukhe: the proof of LAW loop_late_stops
#
# PROOF: each step is rewritten to the advance past the failure cap with the
# deadline test replaced by True, the premise (lb.go_time, lb.ran_time);
# funded and not spent, the halt computes to out-of-time and the advance to
# that report and end.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_late_stops(i, n, dl, c, b, f, x, ev, now, hg, hf, hl):
  +j = i
  +g = hg
  +q = hf
  +t = hl
  (%LALoopBounds.lb.go_time(True{}, c, ev, j, f, Some{1n+n}, dl, b, x, now, True{}, g, q, t) : {(S.act(_), S.phase(S.state(_))) == (Lp.Report{Lp.OutOfTime{}}, Lp.Ended{Lp.OutOfTime{}}) : Lp.Act & Lp.Phase}; {==},
   %LALoopBounds.lb.go_time(True{}, c, ev, j, f, None{}, dl, b, x, now, True{}, g, q, t) : {(S.act(_), S.phase(S.state(_))) == (Lp.Report{Lp.OutOfTime{}}, Lp.Ended{Lp.OutOfTime{}}) : Lp.Act & Lp.Phase}; {==},
   %LALoopBounds.lb.ran_time(True{}, j, Some{1n+n}, dl, b, f, x, now, True{}, t) : {(S.act(_), S.phase(S.state(_))) == (Lp.Report{Lp.OutOfTime{}}, Lp.Ended{Lp.OutOfTime{}}) : Lp.Act & Lp.Phase}; {==},
   %LALoopBounds.lb.ran_time(True{}, j, None{}, dl, b, f, x, now, True{}, t) : {(S.act(_), S.phase(S.state(_))) == (Lp.Report{Lp.OutOfTime{}}, Lp.Ended{Lp.OutOfTime{}}) : Lp.Act & Lp.Phase}; {==})
