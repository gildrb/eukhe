# eukhe: the proof of LAW wait_any_once
#
# PROOF: a fresh job has one delivery left, and no events deliver more than what is left (wa.once_go).

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny
import ./base.bend as LW


def WaitAny.wait_any_once(wake, es):
  LW.wa.once_go(es, wake, Wa.fresh())
