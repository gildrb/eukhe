# eukhe: the proof of LAW gateway_runs_unprotected
# By cases on the model's head test `within`: a step within the auto set
# goes unasked; any other goes the phone's route, the gateway rule,
# which guards only effect 5 (the laws' membership is Tl.elem: pge.in).

import Base
import ../../bend/approvals.bend as Am
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ./base.bend as LA

def gwr.by(w: Bool, +es: List<&2, Nat>, +above: List<&2, Am.Desk>, np: {Tl.elem(es, 5n) == False{} : Bool}) -> {Tools.gw_runs(Am.gate.by(w, es, Am.Phone{} <> above)) == True{} : Bool}:
  match w:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, Tl.elem(es, 5n), False{}, np) : {Tools.gw_fate_runs(Am.guard(_)) == True{} : Bool}
      {==}

def Tools.gateway_runs_unprotected(auto, es, not_protected, above):
  gwr.by(Tl.within(es, auto), es, above, Equal.trans(Bool, Tl.elem(es, 5n), Tools.tg_in(es, 5n), False{}, LA.pge.in(es, 5n), not_protected))
