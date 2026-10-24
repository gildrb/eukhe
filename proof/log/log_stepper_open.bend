# eukhe: the proof of LAW log_stepper_open
#
# Both values of fsync compute.

import Base
import ../../laws/log.bend as Log

def Log.log_stepper_open(fsync):
  match fsync:
    case True{}:
      {==}
    case False{}:
      {==}
