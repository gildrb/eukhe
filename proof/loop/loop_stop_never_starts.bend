# eukhe: the proof of LAW loop_stop_never_starts
#
# PROOF: the premise is rewritten into the goal (lj.IfN); lj.stop_idle
# splits the phase: off or ended, Lp.stop keeps the state and rests; on, the
# premise is True.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/judged.bend as LALoopJudged

def Loop.loop_stop_never_starts(s, off):
  %off : LALoopJudged.lj.IfN(_, {Lp.step(s, Lp.Stop{}) == (s, Lp.Rest{}) : Lp.St & Lp.Act})
  LALoopJudged.lj.stop_idle(s)
