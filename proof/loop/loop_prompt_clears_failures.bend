# eukhe: the proof of LAW loop_prompt_clears_failures
#
# PROOF: the premise is rewritten into the goal (lj.If); the phase is
# split: on, Lp.prompt computes to the adopted turn with no failure; off
# or ended, the premise is False.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/judged.bend as LALoopJudged

def lc.cleared(s: Lp.St, -t: String) -> LALoopJudged.lj.If(S.is_on(S.phase(s)), {S.fails(S.next(s, Lp.Prompt{t})) == 0n : Nat}):
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

def Loop.loop_prompt_clears_failures(s, t, on):
  %on : LALoopJudged.lj.If(_, {S.fails(S.next(s, Lp.Prompt{t})) == 0n : Nat})
  lc.cleared(s, t)
