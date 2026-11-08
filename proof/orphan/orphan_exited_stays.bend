# eukhe: the proof of LAW orphan_exited_stays

import Base
import ../../bend/orphan.bend as Or
import ../../laws/orphan.bend as Orphan
import ./base.bend as LAOrphan

# run over the longer history: one more step on the exited state
def ps.exited_stays(+window: Nat, +evs: List<&2, Or.Ev>, +e: Or.Ev, -d: Or.Out, out: {Or.run(window, evs) == Or.Exited{d} : Or.St}) -> {Or.run(window, LAOrphan.oh.snoc(evs, e)) == Or.Exited{d} : Or.St}:
  %Equal.sym(Or.St, Or.go(window, LAOrphan.oh.snoc(evs, e), Or.Live{Or.W.empty()}), Or.step(window, Or.run(window, evs), e), LAOrphan.oh.go_snoc(window, evs, e, Or.Live{Or.W.empty()})) : {_ == Or.Exited{d} : Or.St}
  %Equal.sym(Or.St, Or.run(window, evs), Or.Exited{d}, out) : {Or.step(window, _, e) == Or.Exited{d} : Or.St}
  {==}

def Orphan.orphan_exited_stays(window, evs, e, d, out):
  ps.exited_stays(window, evs, e, d, out)
