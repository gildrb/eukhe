# eukhe: the proof of LAW loop_unruled_ends
#
# PROOF: the check is the loop's own (lj.judged_own), so the step is
# Lp.judged.mine of an idle session; with a stated condition it is
# Lp.judged.verdict of Lp.said on Unruled, which is Broken: the step
# computes to the ended state and its report.

import Base
import ../../bend/loop.bend as Lp
import ../../laws/loop/model.bend as Loop
import ./base/judged.bend as LALoopJudged

def Loop.loop_unruled_ends(i, l, d, u, t, b, f, x, now, fu):
  %LALoopJudged.lj.judged_own(i, l, d, Lp.Stated{u, t}, b, f, x, Lp.Unruled{}, False{}, now, fu) : {_ == (Lp.St{Lp.Ended{Lp.CheckBroke{}}, i, l, d, Lp.Stated{u, t}, b, f, Lp.Check{i, Lp.Unruled{}}}, Lp.Report{Lp.CheckBroke{}}) : Lp.St & Lp.Act}
  {==}
