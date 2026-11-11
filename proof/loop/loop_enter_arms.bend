# eukhe: the proof of LAW loop_enter_arms
#
# PROOF: the premise is rewritten into the goal (lj.IfN); lj.enter_arms
# splits the phase: off or ended, Lp.start computes to the armed loop; on,
# the premise is True.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/judged.bend as LALoopJudged

def Loop.loop_enter_arms(s, lim, c, now, off):
  %off : LALoopJudged.lj.IfN(_, {(S.does(s, Lp.Enter{lim, c, None{}, now}), (S.phase(S.next(s, Lp.Enter{lim, c, None{}, now})), S.cond(S.next(s, Lp.Enter{lim, c, None{}, now})))) == (Lp.Rest{}, (Lp.Armed{}, c)) : Lp.Act & (Lp.Phase & Lp.Cond)})
  LALoopJudged.lj.enter_arms(s, lim, c, now)
