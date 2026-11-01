# eukhe: the proof of LAW headless_exit_gave_up_before_run
#
# PROOF: without a failed command, a give-up is the cause before the run is read.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit

def HeadlessExit.headless_exit_gave_up_before_run(r, p, c, a):
  {==}
