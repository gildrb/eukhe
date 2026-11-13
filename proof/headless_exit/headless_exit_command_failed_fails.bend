# eukhe: the proof of LAW headless_exit_command_failed_fails
#
# PROOF: a failed command is the cause before anything is read, and its code is 1.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit

def HeadlessExit.headless_exit_command_failed_fails(w, r, p, c, a, ba):
  {==}
