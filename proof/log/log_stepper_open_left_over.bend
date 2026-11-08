# eukhe: the proof of LAW log_stepper_open_left_over
#
# The Bool reads back (it computes once known); the end check sees the
# char left and answers the left-over error.

import Base
import ../../laws/log.bend as Log

def Log.log_stepper_open_left_over(fsync, c, t):
  match fsync:
    case True{}:
      {==}
    case False{}:
      {==}
