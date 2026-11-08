# eukhe: the proof of LAW wait_any_unwatch_hands_on
#
# PROOF: closed in the event and the phase: each step computes.

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny

def WaitAny.wait_any_unwatch_hands_on(wake, w):
  {==}
