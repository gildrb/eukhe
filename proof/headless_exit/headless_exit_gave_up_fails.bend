# eukhe: the proof of LAW headless_exit_gave_up_fails
#
# PROOF: a failed command or a give-up is the cause before the run is read; both have code 1.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit

def HeadlessExit.headless_exit_gave_up_fails(cf, r, p, c, a):
  match cf:
    case True{}:
      {==}
    case False{}:
      {==}
