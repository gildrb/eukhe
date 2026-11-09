# eukhe: the proof of LAW orphan_exit_holds_work: an exit at one more event
# after a live history is the machine's exit with its folds' work, which is
# the declared work

import Base
import ../../bend/orphan.bend as Or
import ../../laws/orphan.bend as Orphan
import ./base.bend as LAOrphan

def ps.exit_holds_work(+window: Nat, +evs: List<&2, Or.Ev>, +e: Or.Ev, -w: Or.W, +live: {Or.run(window, evs) == Or.Live{w} : Or.St}, -d: Or.Out, out: {Or.run(window, LAOrphan.oh.snoc(evs, e)) == Or.Exited{d} : Or.St}) -> {d == LAOrphan.oh.held(Orphan.orphan_declared_busy(LAOrphan.oh.snoc(evs, e))) : Or.Out}:
  %LAOrphan.oh.busy_eq(LAOrphan.oh.snoc(evs, e)) : {d == LAOrphan.oh.held(_) : Or.Out}
  LAOrphan.oh.after_exited(Orphan.orphan_due(window, LAOrphan.oh.snoc(evs, e)), Orphan.orphan_busy(LAOrphan.oh.snoc(evs, e)), LAOrphan.oh.state(LAOrphan.oh.snoc(evs, e)), d,
    Equal.trans(Or.St, LAOrphan.oh.after(window, LAOrphan.oh.snoc(evs, e)), Or.run(window, LAOrphan.oh.snoc(evs, e)), Or.Exited{d},
      Equal.sym(Or.St, Or.run(window, LAOrphan.oh.snoc(evs, e)), LAOrphan.oh.after(window, LAOrphan.oh.snoc(evs, e)), LAOrphan.oh.next_live(window, evs, e, w, live)),
      out))

def Orphan.orphan_exit_holds_work(window, evs, e, w, live, d, out):
  ps.exit_holds_work(window, evs, e, w, live, d, out)
