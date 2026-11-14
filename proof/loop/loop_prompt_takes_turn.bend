# eukhe: the proof of LAW loop_prompt_takes_turn
#
# PROOF: the premise is rewritten into the goal (lb.When); the phase is
# split: off and ended leave no goal (the premise is False), every phase
# of a loop that is on computes to the adopted turn.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def lpt.G(p: Lp.Phase, i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, c: Lp.Cond, b: String, f: Nat, x: Lp.Last, t: String) -> Type:
  {Lp.step(Lp.St{p, i, l, d, c, b, f, x}, Lp.Prompt{t}) == (Lp.St{Lp.Turn{}, 1n+i, l, d, c, t, 0n, x}, Lp.Adopt{1n+i}) : Lp.St & Lp.Act}

def lpt.on(p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, -t: String) -> LALoopBounds.lb.When(S.is_on(p), lpt.G(p, i, l, d, c, b, f, x, t)):
  match p:
    case Lp.Off{}:
      Unit{}
    case Lp.Armed{}:
      {==}
    case Lp.Turn{}:
      {==}
    case Lp.Judging{}:
      {==}
    case Lp.Paused{}:
      {==}
    case Lp.Ended{w}:
      Unit{}

def Loop.loop_prompt_takes_turn(p, i, l, d, c, b, f, x, t, on):
  %on : LALoopBounds.lb.When(_, lpt.G(p, i, l, d, c, b, f, x, t))
  lpt.on(p, i, l, d, c, b, f, x, t)
