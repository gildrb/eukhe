# eukhe: the proof of LAW stop_pending_pauses
#
# PROOF: the claim computes.

import Base
import ../../bend/stop.bend as S
import ../../bend/ffi_stop.bend as FS
import ../../bend/wire.bend as Wr
import ../../laws/stop.bend as Stop

def Stop.stop_pending_pauses():
  {==}
