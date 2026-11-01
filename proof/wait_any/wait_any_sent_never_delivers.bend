# eukhe: the proof of LAW wait_any_sent_never_delivers
#
# PROOF: case analysis on the event: a sent phase answers no delivery.

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny
import ./base.bend as LW


def WaitAny.wait_any_sent_never_delivers(wake, w, e):
  match e:
    case Wa.Watch{}:
      {==}
    case Wa.Unwatch{}:
      {==}
    case Wa.Settles{}:
      {==}
    case Wa.Taken{}:
      {==}
