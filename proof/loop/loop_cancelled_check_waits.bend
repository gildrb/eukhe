# eukhe: the proof of LAW loop_cancelled_check_waits
#
# PROOF: the check is the loop's own (lj.judged_own), so the step is
# Lp.judged.mine; the premise is rewritten into the goal and lj.cancelled
# splits the condition: with one, the verdict of Cancelled is Unjudged and
# the state is kept.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/judged.bend as LALoopJudged

def Loop.loop_cancelled_check_waits(i, l, d, c, b, f, x, now, fu, hc):
  %LALoopJudged.lj.judged_own(i, l, d, c, b, f, x, Lp.Cancelled{}, False{}, now, fu) : {_ == (Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}, Lp.Rest{}) : Lp.St & Lp.Act}
  %hc : LALoopJudged.lj.If(_, {Lp.judged.mine(False{}, i, l, d, c, b, f, x, Lp.Cancelled{}, now, fu) == (Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}, Lp.Rest{}) : Lp.St & Lp.Act})
  LALoopJudged.lj.cancelled(c, i, l, d, b, f, x, now, fu)
