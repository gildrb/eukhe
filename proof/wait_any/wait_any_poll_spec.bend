# eukhe: the proof of LAW wait_any_poll_spec
#
# PROOF: the code's first settled index is the spec's position (wa.first0), its live test the spec's running count (wa.live_running); the last step agrees case by case (wa.poll_of).

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny
import ./base.bend as LW


def WaitAny.wait_any_poll_spec(named, cancel, late, ts):
  %LW.wa.first0(ts, named) : {Wa.poll.found(_, Wa.live(ts), cancel, late) == WaSpec.poll(named, cancel, late, ts) : Wa.Pick}
  %LW.wa.live_running(ts) : {Wa.poll.found(WaSpec.pos(ts, named), _, cancel, late) == WaSpec.poll(named, cancel, late, ts) : Wa.Pick}
  LW.wa.poll_of(WaSpec.pos(ts, named), Nat.is_eq(WaSpec.running(ts), 0n), cancel, late)
