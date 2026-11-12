# eukhe: the proof of LAW task_life_live_steps
#
# PROOF: case on the state. A pending, running or waiting task carries the
# checkpoint the premise names (Some is one to one: tlb.some_inj), so a
# reservation runs it there; a settle and a finalize compute. A held or
# terminal state has no checkpoint: the premise None == Some{c} is false.

import Base
import ../../bend/task_life.bend as Tl
import ../../spec/durable/task_life.bend as Sp
import ../../laws/task_life.bend as TaskLife
import ./base.bend as LB

def tll.G(+s: Tl.St, +c: Nat, +o: Tl.Outcome, h: Bool) -> Type:
  {Tl.step(s, Tl.Reserve{}) == Done{Tl.Running{c}} : Result<&2, &2, Tl.Why, Tl.St>} & ({Tl.step(s, Tl.Settle{o, True{}}) == Done{Tl.Completing{o}} : Result<&2, &2, Tl.Why, Tl.St>} & ({Tl.step(s, Tl.Settle{o, False{}}) == Done{Tl.Terminal{o}} : Result<&2, &2, Tl.Why, Tl.St>} & {Tl.step(s, Tl.Finalize{h}) == Fail{Tl.NotHeld{}} : Result<&2, &2, Tl.Why, Tl.St>}))

# a reservation at the premise's checkpoint
def tll.run(+x: Nat, +c: Nat, e: {Some{x} == Some{c} : Maybe<&2, Nat>}) -> {Done{Tl.Running{x}} == Done{Tl.Running{c}} : Result<&2, &2, Tl.Why, Tl.St>}:
  Equal.cong(Nat, Result<&2, &2, Tl.Why, Tl.St>, z => Done{Tl.Running{z}}, x, c, LB.tlb.some_inj(Nat, x, c, e))

def TaskLife.task_life_live_steps(s, c, o, h, live):
  match s:
    case Tl.Pending{+x}:
      (tll.run(x, c, live), ({==}, ({==}, {==})))
    case Tl.Running{+x}:
      (tll.run(x, c, live), ({==}, ({==}, {==})))
    case Tl.Waiting{+x, p}:
      (tll.run(x, c, live), ({==}, ({==}, {==})))
    case Tl.Completing{q}:
      LB.tlb.none_some(Nat, c, tll.G(Tl.Completing{q}, c, o, h), live)
    case Tl.Terminal{q}:
      LB.tlb.none_some(Nat, c, tll.G(Tl.Terminal{q}, c, o, h), live)
