# eukhe: the proof of LAW orphan_next_by_history

import Base
import ../../bend/orphan.bend as Or
import ../../laws/orphan.bend as Orphan
import ./base.bend as LAOrphan

# run over the longer history: one more step on the live state, which is
# the history's state
def ps.next_by_history(+window: Nat, +evs: List<&2, Or.Ev>, +e: Or.Ev, -w: Or.W, +live: {Or.run(window, evs) == Or.Live{w} : Or.St}) -> {Or.run(window, LAOrphan.oh.snoc(evs, e)) == Orphan.orphan_after(window, LAOrphan.oh.snoc(evs, e)) : Or.St}:
  %Equal.sym(Or.St, Or.go(window, LAOrphan.oh.snoc(evs, e), Or.Live{Or.W.empty()}), Or.step(window, Or.run(window, evs), e), LAOrphan.oh.go_snoc(window, evs, e, Or.Live{Or.W.empty()})) : {_ == Orphan.orphan_after(window, LAOrphan.oh.snoc(evs, e)) : Or.St}
  %Equal.sym(Or.St, Or.run(window, evs), Or.Live{w}, live) : {Or.step(window, _, e) == Orphan.orphan_after(window, LAOrphan.oh.snoc(evs, e)) : Or.St}
  %Equal.sym(Or.W, w, Orphan.orphan_state(evs), LAOrphan.oh.inv_state(window, evs, w, LAOrphan.oh.live(window, evs, w, live))) : {Or.check(window, Or.apply(_, e)) == Orphan.orphan_after(window, LAOrphan.oh.snoc(evs, e)) : Or.St}
  LAOrphan.oh.next(window, evs, e)

def Orphan.orphan_next_by_history(window, evs, e, w, live):
  ps.next_by_history(window, evs, e, w, live)
