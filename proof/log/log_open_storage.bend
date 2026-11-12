# eukhe: the proof of LAW log_open_storage
#
# Both values of fsync compute.

import Base
import ../../laws/log.bend as Log

def Log.log_open_storage(fsync):
  match fsync:
    case True{}:
      {==}
    case False{}:
      {==}
