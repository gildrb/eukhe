# eukhe: the proof of LAW child_report_move

import Base
import ../../bend/child.bend as Ch
import ../../laws/child/model.bend as Child

def Child.child_report_move(f, n):
  match f:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case Ch.Queued{}:
          {==}
        case Ch.Withdrawn{}:
          {==}
        case Ch.Placed{}:
          {==}
        case Ch.Read{}:
          {==}
