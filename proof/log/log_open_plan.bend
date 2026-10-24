# eukhe: the proof of LAW log_open_plan
#
# Both values of fsync compute.

import Base
import ../../laws/log.bend as Log

def Log.log_open_plan(fsync):
  match fsync:
    case True{}:
      {==}
    case False{}:
      {==}
