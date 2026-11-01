# eukhe: the proof of LAW wait_any_settle_routes
#
# PROOF: the settle of a live job is deliver over the code's route, which is the spec's (wa.route_eq).

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny
import ./base.bend as LW


def WaitAny.wait_any_settle_routes(w, wake):
  %LW.wa.route_eq(Wa.watched(w), wake) : {Wa.deliver(Wa.route(Wa.watched(w), wake), w) == Wa.deliver(_, w) : Wa.Out}
  {==}
