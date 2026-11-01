# eukhe: the proof of LAW wait_any_route_spec
#
# PROOF: case analysis (wa.route_eq).

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny
import ./base.bend as LW


def WaitAny.wait_any_route_spec(watched, wake):
  LW.wa.route_eq(watched, wake)
