# eukhe: the proof of LAW headless_exit_command_failed_first
#
# PROOF: a failed command is the cause before anything else is read.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit

def HeadlessExit.headless_exit_command_failed_first(w, r, p, c, a, ba):
  {==}
