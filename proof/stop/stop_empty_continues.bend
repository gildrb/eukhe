# eukhe: the proof of LAW stop_empty_continues
#
# PROOF: the claim computes.

import Base
import ../../bend/stop.bend as S
import ../../bend/ffi_stop.bend as FS
import ../../bend/wire.bend as Wr
import ../../laws/stop.bend as Stop

def Stop.stop_empty_continues(b, p, sp, cu):
  {==}
