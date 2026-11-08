# eukhe: the proof of LAW wait_any_refuses_idle
#
# PROOF: with no target counted as settled the code finds no index
# (wap.none_first) and its live test is the spec's some_runs
# (wap.live_runs), here False: the poll is refused.

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny
import ./base/poll.bend as LWP

def WaitAny.wait_any_refuses_idle(named, cancel, late, ts, none, idle):
  LWP.wap.unsettled(named, cancel, late, ts, False{}, LWP.wap.none_first(ts, named, 0n, none), Equal.trans(Bool, Wa.live(ts), WaSpec.some_runs(ts), False{}, LWP.wap.live_runs(ts), idle))
