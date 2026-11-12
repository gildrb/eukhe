# eukhe: the proof of LAW loop_confirmed_ends
#
# PROOF: the check is the loop's own (lj.judged_own), so the step is
# Lp.judged.mine; the premise is rewritten into the goal and lj.confirmed
# splits the condition and the evidence: the two confirming cases compute,
# the others have a False premise.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/judged.bend as LALoopJudged

def Loop.loop_confirmed_ends(i, l, d, c, b, f, x, ev, now, fu, h):
  %LALoopJudged.lj.judged_own(i, l, d, c, b, f, x, ev, False{}, now, fu) : {_ == (Lp.St{Lp.Ended{Lp.Satisfied{}}, i, l, d, c, b, f, Lp.Check{i, ev}}, Lp.Report{Lp.Satisfied{}}) : Lp.St & Lp.Act}
  %h : LALoopJudged.lj.If(_, {Lp.judged.mine(False{}, i, l, d, c, b, f, x, ev, now, fu) == (Lp.St{Lp.Ended{Lp.Satisfied{}}, i, l, d, c, b, f, Lp.Check{i, ev}}, Lp.Report{Lp.Satisfied{}}) : Lp.St & Lp.Act})
  LALoopJudged.lj.confirmed(c, ev, i, l, d, b, f, x, now, fu)
