# eukhe: the proof of LAW task_life_only_running_commits
#
# PROOF: case on the state. Pending and waiting refuse both as not
# running (they compute); a running state contradicts the premise idle, a
# held or terminal one the premise live (Some{q} == None).

import Base
import ../../bend/task_life.bend as Tl
import ../../spec/durable/task_life.bend as Sp
import ../../laws/task_life.bend as TaskLife
import ./base.bend as LB

def tlo.G(+s: Tl.St, n: Tl.Next, h: Bool) -> Type:
  {Tl.step(s, Tl.Commit{n, h}) == Fail{Tl.NotRunning{}} : Result<&2, &2, Tl.Why, Tl.St>} & {Tl.step(s, Tl.Requeue{}) == Fail{Tl.NotRunning{}} : Result<&2, &2, Tl.Why, Tl.St>}

def TaskLife.task_life_only_running_commits(s, n, h, live, idle):
  match s:
    case Tl.Pending{x}:
      ({==}, {==})
    case Tl.Running{x}:
      LB.tlb.absurd_tf(tlo.G(Tl.Running{x}, n, h), idle)
    case Tl.Waiting{x, p}:
      ({==}, {==})
    case Tl.Completing{q}:
      LB.tlb.some_none(Tl.Outcome, q, tlo.G(Tl.Completing{q}, n, h), live)
    case Tl.Terminal{q}:
      LB.tlb.some_none(Tl.Outcome, q, tlo.G(Tl.Terminal{q}, n, h), live)
