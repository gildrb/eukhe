# eukhe: the proof of LAW log_stepper_open_left_over
#
# How the storage opens reads back (it computes once known); the end check
# sees the char left and answers the left-over error.

import Base
import ../../bend/log.bend as Lr
import ../../laws/log.bend as Log

def Log.log_stepper_open_left_over(h, c, t):
  match h:
    case Lr.Unsynced{}:
      {==}
    case Lr.Synced{}:
      {==}
    case Lr.Stamped{kept}:
      match kept:
        case True{}:
          {==}
        case False{}:
          {==}
