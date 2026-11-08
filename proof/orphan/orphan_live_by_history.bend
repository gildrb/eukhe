# eukhe: the proof of LAW orphan_live_by_history: a live worker's state is
# its folds' state (the run invariant), which agrees with the declared
# state on every history (each declared field takes the machine's step on
# one more event)

import Base
import ../../bend/orphan.bend as Or
import ../../laws/orphan.bend as Orphan
import ./base.bend as LAOrphan

def ps.live_by_history(+window: Nat, +evs: List<&2, Or.Ev>, -w: Or.W, live: {Or.run(window, evs) == Or.Live{w} : Or.St}) -> {w == Orphan.orphan_declared(evs) : Or.W}:
  Equal.trans(Or.W, w, LAOrphan.oh.state(evs), Orphan.orphan_declared(evs), LAOrphan.oh.inv_state(window, evs, w, LAOrphan.oh.live(window, evs, w, live)), LAOrphan.oh.agree(evs))

def Orphan.orphan_live_by_history(window, evs, w, live):
  ps.live_by_history(window, evs, w, live)
