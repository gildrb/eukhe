# eukhe: the proof of LAW loop_broken_check_ends
#
# PROOF: the check is the loop's own (lj.judged_own), so the step is
# Lp.judged.mine; the four premises are rewritten into the goal as one Bool
# (lj.broken_if) and lj.broken splits the condition and the evidence: each
# case computes to the broken end, or a premise is False.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/judged.bend as LALoopJudged

def Loop.loop_broken_check_ends(i, l, d, c, b, f, x, ev, now, fu, hc, hd, hs, hg):
  %LALoopJudged.lj.judged_own(i, l, d, c, b, f, x, ev, False{}, now, fu) : {(S.act(_), S.phase(S.state(_))) == (Lp.Report{Lp.CheckBroke{}}, Lp.Ended{Lp.CheckBroke{}}) : Lp.Act & Lp.Phase}
  %LALoopJudged.lj.broken_if(c, ev, hc, hd, hs, hg) : LALoopJudged.lj.If(_, {(S.act(Lp.judged.mine(False{}, i, l, d, c, b, f, x, ev, now, fu)), S.phase(S.state(Lp.judged.mine(False{}, i, l, d, c, b, f, x, ev, now, fu)))) == (Lp.Report{Lp.CheckBroke{}}, Lp.Ended{Lp.CheckBroke{}}) : Lp.Act & Lp.Phase})
  LALoopJudged.lj.broken(c, ev, i, l, d, b, f, x, now, fu)
