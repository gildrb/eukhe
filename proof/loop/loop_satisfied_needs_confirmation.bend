# eukhe: the proof of LAW loop_satisfied_needs_confirmation
#
# PROOF: the premise is rewritten into the goal (lj.If); lj.sat splits the
# event and the phase: the premise computes to False everywhere but at a
# judged check of a judging loop, where lj.judged_sat splits the evidence:
# only the confirming exit status ends satisfied.

import Base
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/judged.bend as LALoopJudged

def Loop.loop_satisfied_needs_confirmation(s, e, h):
  %h : LALoopJudged.lj.If(_, {S.confirms(s, e) == True{} : Bool})
  LALoopJudged.lj.sat(e, s)
