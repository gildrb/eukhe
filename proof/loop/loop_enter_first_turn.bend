# eukhe: the proof of LAW loop_enter_first_turn
#
# PROOF: the premise is rewritten into the goal (lj.IfN); lj.enter_first
# splits the phase: off or ended, Lp.start computes to the first turn; on,
# the premise is True.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/judged.bend as LALoopJudged

def Loop.loop_enter_first_turn(s, lim, c, t, now, off):
  %off : LALoopJudged.lj.IfN(_, {(S.does(s, Lp.Enter{lim, c, Some{t}, now}), (S.phase(S.next(s, Lp.Enter{lim, c, Some{t}, now})), (S.body(S.next(s, Lp.Enter{lim, c, Some{t}, now})), S.cond(S.next(s, Lp.Enter{lim, c, Some{t}, now}))))) == (Lp.Submit{1n, t}, (Lp.Turn{}, (t, c))) : Lp.Act & (Lp.Phase & (String & Lp.Cond))})
  LALoopJudged.lj.enter_first(s, lim, c, t, now)
