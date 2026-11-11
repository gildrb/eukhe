# eukhe: the proof of LAW loop_settled_turn_is_judged
#
# PROOF: the turn is the loop's own (lj.settled_own), so the step is
# Lp.settled.mine; the two premises are rewritten into the goal as one Bool
# and lj.settled_judged splits the condition and the outcome: each case
# computes to Judge{i} and Judging, or its premise is False.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/judged.bend as LALoopJudged

def Loop.loop_settled_turn_is_judged(i, l, d, c, b, f, x, o, now, fu, hc, ho):
  %LALoopJudged.lj.settled_own(i, l, d, c, b, f, x, o, False{}, now, fu) : {(S.act(_), S.phase(S.state(_))) == (Lp.Judge{i}, Lp.Judging{}) : Lp.Act & Lp.Phase}
  %LALoopJudged.lj.and2(S.has_cond(c), Bool.not(S.out_halted(o)), hc, LALoopJudged.lj.not_t(S.out_halted(o), ho)) : LALoopJudged.lj.If(_, {(S.act(Lp.settled.mine(False{}, o, i, l, d, c, b, f, x, now, fu)), S.phase(S.state(Lp.settled.mine(False{}, o, i, l, d, c, b, f, x, now, fu)))) == (Lp.Judge{i}, Lp.Judging{}) : Lp.Act & Lp.Phase})
  LALoopJudged.lj.settled_judged(c, o, i, l, d, b, f, x, now, fu)
