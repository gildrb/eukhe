# eukhe: the proof of LAW loop_abort_pauses
#
# PROOF: the premise is rewritten into the goal (lj.If); the phase is
# split: on, Lp.abort computes to the pause; off or ended, the premise is
# False.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/judged.bend as LALoopJudged

def la.G(s: Lp.St) -> Type:
  {(S.does(s, Lp.Abort{}), (S.phase(S.next(s, Lp.Abort{})), (S.iter(S.next(s, Lp.Abort{})), (S.left(S.next(s, Lp.Abort{})), (S.deadline(S.next(s, Lp.Abort{})), (S.cond(S.next(s, Lp.Abort{})), S.last(S.next(s, Lp.Abort{})))))))) == (Lp.Rest{}, (Lp.Paused{}, (S.iter(s), (S.left(s), (S.deadline(s), (S.cond(s), S.last(s))))))) : Lp.Act & (Lp.Phase & (Nat & (Maybe<&2, Nat> & (Maybe<&2, Nat> & (Lp.Cond & Lp.Last)))))}

def la.paused(s: Lp.St) -> LALoopJudged.lj.If(S.is_on(S.phase(s)), la.G(s)):
  match s:
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      Unit{}

def Loop.loop_abort_pauses(s, on):
  %on : LALoopJudged.lj.If(_, la.G(s))
  la.paused(s)
