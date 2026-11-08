# eukhe: the proof of LAW orphan_live_not_due

import Base
import ../../bend/orphan.bend as Or
import ../../laws/orphan.bend as Orphan
import ./base.bend as LAOrphan

def ps.live_not_due(+window: Nat, +evs: List<&2, Or.Ev>, -w: Or.W, live: {Or.run(window, evs) == Or.Live{w} : Or.St}) -> {Orphan.orphan_due(window, evs) == False{} : Bool}:
  LAOrphan.oh.inv_due(window, evs, w, LAOrphan.oh.live(window, evs, w, live))

def Orphan.orphan_live_not_due(window, evs, w, live):
  ps.live_not_due(window, evs, w, live)
