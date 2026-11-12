# eukhe: the proof of LAW loop_auto_needs_refutation
#
# PROOF: the premise is rewritten into the goal (lj.If); lj.auto splits the
# event and the phase: a Submit comes only from a settled turn with no
# condition, or from a judged check of a judging loop, where lj.judged_auto
# splits the evidence: only the refuting status advances.

import Base
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/judged.bend as LALoopJudged

def Loop.loop_auto_needs_refutation(s, e, h):
  %h : LALoopJudged.lj.If(_, {S.refutes(s, e) == True{} : Bool})
  LALoopJudged.lj.auto(e, s)
