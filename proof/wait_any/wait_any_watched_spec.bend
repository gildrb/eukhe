# eukhe: the proof of LAW wait_any_watched_spec
#
# PROOF: case analysis on the watchers.

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny
import ./base.bend as LW


def WaitAny.wait_any_watched_spec(w):
  match w:
    case 0n:
      {==}
    case 1n+q:
      {==}
