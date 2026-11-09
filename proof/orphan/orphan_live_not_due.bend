# eukhe: the proof of LAW orphan_live_not_due: a live run keeps the
# invariant that its last exit check was not due (oh.live); on a history
# and one more event that check is the test on the machine's folds
# (oh.due_snoc), whose work and absence are the declared ones (oh.busy_eq,
# oh.absent_eq)

import Base
import ../../bend/orphan.bend as Or
import ../../laws/orphan.bend as Orphan
import ./base.bend as LAOrphan

def ps.live_not_due(+window: Nat, +evs: List<&2, Or.Ev>, +e: Or.Ev, -w: Or.W, live: {Or.run(window, LAOrphan.oh.snoc(evs, e)) == Or.Live{w} : Or.St}) -> {Orphan.orphan_due_by(window, Orphan.orphan_declared_busy(LAOrphan.oh.snoc(evs, e)), Orphan.orphan_unanswered_ms(LAOrphan.oh.snoc(evs, e))) == False{} : Bool}:
  %LAOrphan.oh.busy_eq(LAOrphan.oh.snoc(evs, e)) : {Orphan.orphan_due_by(window, _, Orphan.orphan_unanswered_ms(LAOrphan.oh.snoc(evs, e))) == False{} : Bool}
  %LAOrphan.oh.absent_eq(LAOrphan.oh.snoc(evs, e)) : {Orphan.orphan_due_by(window, LAOrphan.oh.folds_busy(LAOrphan.oh.snoc(evs, e)), _) == False{} : Bool}
  %Equal.sym(Bool, Orphan.orphan_due_by(window, LAOrphan.oh.folds_busy(LAOrphan.oh.snoc(evs, e)), LAOrphan.oh.absent(0n, LAOrphan.oh.snoc(evs, e))), LAOrphan.oh.due_at(window, LAOrphan.oh.snoc(evs, e)), LAOrphan.oh.due_snoc(window, evs, e)) : {_ == False{} : Bool}
  LAOrphan.oh.inv_due(window, LAOrphan.oh.snoc(evs, e), w, LAOrphan.oh.live(window, LAOrphan.oh.snoc(evs, e), w, live))

def Orphan.orphan_live_not_due(window, evs, e, w, live):
  ps.live_not_due(window, evs, e, w, live)
