# eukhe: the proof of LAW child_report_move_is_owe

import Base
import ../../bend/child.bend as Ch
import ../../LAWS.bend as Laws

def Laws.child_report_move_is_owe(f, k, n, open, inbox):
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
