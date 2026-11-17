# eukhe: the proof of LAW log_open_storage
#
# Every way to open computes.

import Base
import ../../bend/log.bend as Lr
import ../../laws/log.bend as Log

def Log.log_open_storage(h):
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
