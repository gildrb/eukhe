# eukhe: the proof of LAW stop_asked_early_example
#
# PROOF: the closed claim computes.

import Base
import ../../bend/stop.bend as S
import ../../bend/ffi_stop.bend as FS
import ../../laws/stop.bend as Stop

def Stop.stop_asked_early_example():
  ({==}, {==})
