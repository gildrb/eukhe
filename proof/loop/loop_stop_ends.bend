# eukhe: the proof of LAW loop_stop_ends
#
# PROOF: the premise is rewritten into the goal (lj.If); lj.stop_ends splits
# the phase: on, Lp.stop computes to the stopped end; off or ended, the
# premise is False.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/judged.bend as LALoopJudged

def Loop.loop_stop_ends(s, on):
  %on : LALoopJudged.lj.If(_, {(S.does(s, Lp.Stop{}), S.phase(S.next(s, Lp.Stop{}))) == (Lp.Report{Lp.Stopped{}}, Lp.Ended{Lp.Stopped{}}) : Lp.Act & Lp.Phase})
  LALoopJudged.lj.stop_ends(s)
