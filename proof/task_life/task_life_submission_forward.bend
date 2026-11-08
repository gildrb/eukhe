# eukhe: the proof of LAW task_life_submission_forward
#
# PROOF: case on the submission and the change: every outcome computes to
# True (a settled submission stays; a move goes up a rank).

import Base
import ../../bend/task_life.bend as Tl
import ../../bend/ffi_task_life.bend as FTl
import ../../bend/submission.bend as Sb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../spec/durable/task_life.bend as Sp
import ../../laws/task_life.bend as TaskLife

def TaskLife.task_life_submission_forward(s, c):
  match s:
    case Sb.InQueued{}:
      match c:
        case Sb.Place{e}:
          {==}
        case Sb.Answer{a}:
          {==}
        case Sb.Drop{}:
          {==}
    case Sb.InPlaced{e}:
      match c:
        case Sb.Place{f}:
          {==}
        case Sb.Answer{a}:
          {==}
        case Sb.Drop{}:
          {==}
    case Sb.InAnswered{e, a}:
      {==}
    case Sb.InDropped{m}:
      {==}
    case Sb.WrQueued{}:
      match c:
        case Sb.Place{e}:
          {==}
        case Sb.Answer{a}:
          {==}
        case Sb.Drop{}:
          {==}
    case Sb.WrPlaced{e}:
      {==}
    case Sb.WrDropped{}:
      {==}
