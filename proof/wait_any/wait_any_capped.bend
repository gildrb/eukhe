# eukhe: the proof of LAW wait_any_capped
#
# PROOF: the cap is within itself (wa.le_refl); a min is within its right side (wa.min_le_r).

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny
import ./base.bend as LW


def WaitAny.wait_any_capped(asked):
  match asked:
    case None{}:
      LW.wa.le_refl(1800n)
    case Some{t}:
      LW.wa.min_le_r(t, 1800n)
