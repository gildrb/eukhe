# eukhe: the proof of LAW stop_reply_stands
#
# PROOF: the closed claims compute.

import Base
import ../../bend/stop.bend as S
import ../../bend/ffi_stop.bend as FS
import ../../bend/wire.bend as Wr
import ../../laws/stop.bend as Stop

def Stop.stop_reply_stands():
  ({==}, {==})
