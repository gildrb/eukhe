# eukhe: the proof of LAW wait_any_fresh_spec
#
# PROOF: closed computation.

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny
import ./base.bend as LW


def WaitAny.wait_any_fresh_spec():
  {==}
