# eukhe: the proof of LAW orphan_live_state

import Base
import ../../bend/orphan.bend as Or
import ../../laws/orphan.bend as Orphan
import ./base.bend as LAOrphan

def ps.live_state(+window: Nat, +evs: List<&2, Or.Ev>, -w: Or.W, live: {Or.run(window, evs) == Or.Live{w} : Or.St}) -> {w == Orphan.orphan_state(evs) : Or.W}:
  LAOrphan.oh.inv_state(window, evs, w, LAOrphan.oh.live(window, evs, w, live))

def Orphan.orphan_live_state(window, evs, w, live):
  ps.live_state(window, evs, w, live)
