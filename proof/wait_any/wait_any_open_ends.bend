# eukhe: the proof of LAW wait_any_open_ends
#
# PROOF: with no target counted as settled the code finds no index
# (wap.none_first) and its live test is the spec's some_runs
# (wap.live_runs), here True: each poll is the code's last step on the
# cancel and the cap, which the three cases compute.

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny
import ./base/poll.bend as LWP

def WaitAny.wait_any_open_ends(named, late, ts, none, runs):
  +nf = LWP.wap.none_first(ts, named, 0n, none)
  +lv = Equal.trans(Bool, Wa.live(ts), WaSpec.some_runs(ts), True{}, LWP.wap.live_runs(ts), runs)
  %Equal.sym(Wa.Pick, Wa.poll(named, True{}, late, ts), Wa.poll.none(True{}, True{}, late), LWP.wap.unsettled(named, True{}, late, ts, True{}, nf, lv)) : {[_, Wa.poll(named, False{}, True{}, ts), Wa.poll(named, False{}, False{}, ts)] == [Wa.Stopped{}, Wa.Capped{}, Wa.Waits{}] : List<&2, Wa.Pick>}
  %Equal.sym(Wa.Pick, Wa.poll(named, False{}, True{}, ts), Wa.poll.none(True{}, False{}, True{}), LWP.wap.unsettled(named, False{}, True{}, ts, True{}, nf, lv)) : {[Wa.poll.none(True{}, True{}, late), _, Wa.poll(named, False{}, False{}, ts)] == [Wa.Stopped{}, Wa.Capped{}, Wa.Waits{}] : List<&2, Wa.Pick>}
  %Equal.sym(Wa.Pick, Wa.poll(named, False{}, False{}, ts), Wa.poll.none(True{}, False{}, False{}), LWP.wap.unsettled(named, False{}, False{}, ts, True{}, nf, lv)) : {[Wa.poll.none(True{}, True{}, late), Wa.poll.none(True{}, False{}, True{}), _] == [Wa.Stopped{}, Wa.Capped{}, Wa.Waits{}] : List<&2, Wa.Pick>}
  {==}
