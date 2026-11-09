# eukhe: the proof of LAW orphan_exits_when_due: one more event after a
# live history is the machine's exit check on the longer history's folds,
# whose work and absence are the declared ones

import Base
import ../../bend/orphan.bend as Or
import ../../laws/orphan.bend as Orphan
import ./base.bend as LAOrphan

def ps.exits_when_due(+window: Nat, +evs: List<&2, Or.Ev>, +e: Or.Ev, -w: Or.W, +live: {Or.run(window, evs) == Or.Live{w} : Or.St}) -> {Orphan.orphan_exited(Or.run(window, LAOrphan.oh.snoc(evs, e))) == Orphan.orphan_due_by(window, Orphan.orphan_declared_busy(LAOrphan.oh.snoc(evs, e)), Orphan.orphan_unanswered_ms(LAOrphan.oh.snoc(evs, e))) : Bool}:
  %Equal.sym(Or.St, Or.run(window, LAOrphan.oh.snoc(evs, e)), LAOrphan.oh.after(window, LAOrphan.oh.snoc(evs, e)), LAOrphan.oh.next_live(window, evs, e, w, live)) : {Orphan.orphan_exited(_) == Orphan.orphan_due_by(window, Orphan.orphan_declared_busy(LAOrphan.oh.snoc(evs, e)), Orphan.orphan_unanswered_ms(LAOrphan.oh.snoc(evs, e))) : Bool}
  %Equal.sym(Bool, Orphan.orphan_exited(LAOrphan.oh.after(window, LAOrphan.oh.snoc(evs, e))), Orphan.orphan_due(window, LAOrphan.oh.snoc(evs, e)), LAOrphan.oh.exited_after(Orphan.orphan_due(window, LAOrphan.oh.snoc(evs, e)), Orphan.orphan_busy(LAOrphan.oh.snoc(evs, e)), LAOrphan.oh.state(LAOrphan.oh.snoc(evs, e)))) : {_ == Orphan.orphan_due_by(window, Orphan.orphan_declared_busy(LAOrphan.oh.snoc(evs, e)), Orphan.orphan_unanswered_ms(LAOrphan.oh.snoc(evs, e))) : Bool}
  %LAOrphan.oh.due_snoc(window, evs, e) : {_ == Orphan.orphan_due_by(window, Orphan.orphan_declared_busy(LAOrphan.oh.snoc(evs, e)), Orphan.orphan_unanswered_ms(LAOrphan.oh.snoc(evs, e))) : Bool}
  %Equal.sym(Bool, Orphan.orphan_busy(LAOrphan.oh.snoc(evs, e)), Orphan.orphan_declared_busy(LAOrphan.oh.snoc(evs, e)), LAOrphan.oh.busy_eq(LAOrphan.oh.snoc(evs, e))) : {Orphan.orphan_due_by(window, _, Orphan.orphan_absent(0n, LAOrphan.oh.snoc(evs, e))) == Orphan.orphan_due_by(window, Orphan.orphan_declared_busy(LAOrphan.oh.snoc(evs, e)), Orphan.orphan_unanswered_ms(LAOrphan.oh.snoc(evs, e))) : Bool}
  %Equal.sym(Nat, Orphan.orphan_absent(0n, LAOrphan.oh.snoc(evs, e)), Orphan.orphan_unanswered_ms(LAOrphan.oh.snoc(evs, e)), LAOrphan.oh.absent_eq(LAOrphan.oh.snoc(evs, e))) : {Orphan.orphan_due_by(window, Orphan.orphan_declared_busy(LAOrphan.oh.snoc(evs, e)), _) == Orphan.orphan_due_by(window, Orphan.orphan_declared_busy(LAOrphan.oh.snoc(evs, e)), Orphan.orphan_unanswered_ms(LAOrphan.oh.snoc(evs, e))) : Bool}
  {==}

def Orphan.orphan_exits_when_due(window, evs, e, w, live):
  ps.exits_when_due(window, evs, e, w, live)
