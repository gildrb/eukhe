# eukhe: the proof of LAW loop_prompt_adopted
#
# PROOF: the premise is rewritten into the goal (lj.If); lj.adopted splits
# the phase: on, Lp.prompt computes to the adopted turn; off or ended, the
# premise is False.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/judged.bend as LALoopJudged

def Loop.loop_prompt_adopted(s, t, on):
  %on : LALoopJudged.lj.If(_, {(S.does(s, Lp.Prompt{t}), (S.phase(S.next(s, Lp.Prompt{t})), (S.body(S.next(s, Lp.Prompt{t})), (S.left(S.next(s, Lp.Prompt{t})), S.cond(S.next(s, Lp.Prompt{t})))))) == (Lp.Adopt{1n+S.iter(s)}, (Lp.Turn{}, (t, (S.left(s), S.cond(s))))) : Lp.Act & (Lp.Phase & (String & (Maybe<&2, Nat> & Lp.Cond)))})
  LALoopJudged.lj.adopted(s, t)
