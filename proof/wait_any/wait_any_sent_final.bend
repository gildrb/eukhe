# eukhe: the proof of LAW wait_any_sent_final
#
# PROOF: case analysis on the event: a sent phase stays sent.

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny

def WaitAny.wait_any_sent_final(wake, w, e):
  match e:
    case Wa.Watch{}:
      {==}
    case Wa.Unwatch{}:
      {==}
    case Wa.Settles{}:
      {==}
    case Wa.Taken{}:
      {==}
