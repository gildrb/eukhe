# eukhe: the proof of LAW loop_enter_ends_running
#
# PROOF: the premise is rewritten into the goal (lj.If); lj.enter_ends
# splits the phase: on, Lp.enter computes to the stopped end; off or ended,
# the premise is False.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/judged.bend as LALoopJudged

def Loop.loop_enter_ends_running(s, lim, c, pr, now, on):
  %on : LALoopJudged.lj.If(_, {(S.does(s, Lp.Enter{lim, c, pr, now}), S.phase(S.next(s, Lp.Enter{lim, c, pr, now}))) == (Lp.Report{Lp.Stopped{}}, Lp.Ended{Lp.Stopped{}}) : Lp.Act & Lp.Phase})
  LALoopJudged.lj.enter_ends(s, lim, c, pr, now)
