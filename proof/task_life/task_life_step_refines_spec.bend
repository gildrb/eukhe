# eukhe: the proof of LAW task_life_step_refines_spec
#
# PROOF: case on the state and the transition: each arm of the rules
# computes to the spec's, an outcome decided by tlb.hold, a commit by
# tlb.commit.

import Base
import ../../bend/task_life.bend as Tl
import ../../bend/ffi_task_life.bend as FTl
import ../../bend/submission.bend as Sb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../spec/durable/task_life.bend as Sp
import ../../laws/task_life.bend as TaskLife
import ./base.bend as LB

def TaskLife.task_life_step_refines_spec(s, e):
  match s:
    case Tl.Pending{c}:
      match e:
        case Tl.Reserve{}:
          {==}
        case Tl.Commit{n, h}:
          {==}
        case Tl.Requeue{}:
          {==}
        case Tl.Settle{o, h}:
          LB.tlb.hold(o, h)
        case Tl.Finalize{h}:
          {==}
    case Tl.Running{c}:
      match e:
        case Tl.Reserve{}:
          {==}
        case Tl.Commit{n, h}:
          LB.tlb.commit(n, h)
        case Tl.Requeue{}:
          {==}
        case Tl.Settle{o, h}:
          LB.tlb.hold(o, h)
        case Tl.Finalize{h}:
          {==}
    case Tl.Waiting{c, p}:
      match e:
        case Tl.Reserve{}:
          {==}
        case Tl.Commit{n, h}:
          {==}
        case Tl.Requeue{}:
          {==}
        case Tl.Settle{o, h}:
          LB.tlb.hold(o, h)
        case Tl.Finalize{h}:
          {==}
    case Tl.Completing{o}:
      match e:
        case Tl.Reserve{}:
          {==}
        case Tl.Commit{n, h}:
          {==}
        case Tl.Requeue{}:
          {==}
        case Tl.Settle{q, h}:
          {==}
        case Tl.Finalize{h}:
          LB.tlb.hold(o, h)
    case Tl.Terminal{o}:
      match e:
        case Tl.Reserve{}:
          {==}
        case Tl.Commit{n, h}:
          {==}
        case Tl.Requeue{}:
          {==}
        case Tl.Settle{q, h}:
          {==}
        case Tl.Finalize{h}:
          {==}
