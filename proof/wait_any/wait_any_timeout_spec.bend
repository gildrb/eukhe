# eukhe: the proof of LAW wait_any_timeout_spec
#
# PROOF: none asked: both are the cap; else the min is the smaller one (wa.min_pick), the spec's pick.

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny
import ./base.bend as LW


def WaitAny.wait_any_timeout_spec(asked):
  match asked:
    case None{}:
      {==}
    case Some{+t}:
      Equal.trans(Nat, Nat.min(t, 1800n), LW.wa.pick(Nat.is_le(t, 1800n), t, 1800n), WaSpec.timeout.of(Nat.is_le(t, 1800n), t), LW.wa.min_pick(t, 1800n), LW.wa.pick_cap(Nat.is_le(t, 1800n), t))
