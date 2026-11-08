# eukhe: the proof of LAW task_life_outcome_once
#
# PROOF: case on the transition: a held task refuses all but a
# finalization, which keeps o held or makes it terminal (case on holds).

import Base
import ../../bend/task_life.bend as Tl
import ../../bend/ffi_task_life.bend as FTl
import ../../bend/submission.bend as Sb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../spec/durable/task_life.bend as Sp
import ../../laws/task_life.bend as TaskLife

def TaskLife.task_life_outcome_once(o, e):
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
      match h:
        case True{}:
          {==}
        case False{}:
          {==}
