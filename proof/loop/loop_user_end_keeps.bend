# eukhe: the proof of LAW loop_user_end_keeps
#
# PROOF: the premise is rewritten into the goal (lb.When); the phase is
# split: off and ended leave no goal (the premise is False), every phase
# of a loop that is on computes, for `/loop` and for a stop, to the
# stopped state with every other field as it was.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def lue.G(p: Lp.Phase, i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, c: Lp.Cond, b: String, f: Nat, x: Lp.Last, lim: Lp.Limit, c2: Lp.Cond, pr: Maybe<&2, String>, now: Nat) -> Type:
  {Lp.step(Lp.St{p, i, l, d, c, b, f, x}, Lp.Enter{lim, c2, pr, now}) == (Lp.St{Lp.Ended{Lp.Stopped{}}, i, l, d, c, b, f, x}, Lp.Report{Lp.Stopped{}}) : Lp.St & Lp.Act} &
  {Lp.step(Lp.St{p, i, l, d, c, b, f, x}, Lp.Stop{}) == (Lp.St{Lp.Ended{Lp.Stopped{}}, i, l, d, c, b, f, x}, Lp.Report{Lp.Stopped{}}) : Lp.St & Lp.Act}

def lue.on(p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, -lim: Lp.Limit, -c2: Lp.Cond, -pr: Maybe<&2, String>, -now: Nat) -> LALoopBounds.lb.When(S.is_on(p), lue.G(p, i, l, d, c, b, f, x, lim, c2, pr, now)):
  match p:
    case Lp.Off{}:
      Unit{}
    case Lp.Armed{}:
      ({==}, {==})
    case Lp.Turn{}:
      ({==}, {==})
    case Lp.Judging{}:
      ({==}, {==})
    case Lp.Paused{}:
      ({==}, {==})
    case Lp.Ended{w}:
      Unit{}

def Loop.loop_user_end_keeps(p, i, l, d, c, b, f, x, lim, c2, pr, now, on):
  %on : LALoopBounds.lb.When(_, lue.G(p, i, l, d, c, b, f, x, lim, c2, pr, now))
  lue.on(p, i, l, d, c, b, f, x, lim, c2, pr, now)
