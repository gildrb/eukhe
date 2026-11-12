# eukhe: the proof of LAW stop_think_room_left_never_compacts
#
# PROOF: room under the window fails the window test (LR.str.bound_room); a failed window test is no compaction (LR.str.no_shrink).

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ./base/recover.bend as LR
import ../../laws/stop/recover.bend as StopRecover

def StopRecover.stop_think_room_left_never_compacts(rc, w, c, p, o, lower, k, row, room):
  LR.str.no_shrink(rc, w, c, p, o, lower, k, row, LR.str.bound_room(w, c, p, o, room))
