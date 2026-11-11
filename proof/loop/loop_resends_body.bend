# eukhe: the proof of LAW loop_resends_body
#
# PROOF: the premise is rewritten into the goal (lj.If); lj.resends splits
# the event and the phase: the only Submit that is not a new `/loop` comes
# from Lp.advance.on (lj.adv_resends), with the state's iteration and
# prompt.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/judged.bend as LALoopJudged

def Loop.loop_resends_body(s, e, h):
  %h : LALoopJudged.lj.If(_, {S.does(s, e) == Lp.Submit{1n+S.iter(s), S.body(s)} : Lp.Act})
  LALoopJudged.lj.resends(e, s)
