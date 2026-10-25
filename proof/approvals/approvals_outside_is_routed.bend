# eukhe: the proof of LAW approvals_outside_is_routed
# PROOF: the gate's first choice is whether the step is within the auto
# set; outside, it is routed (a case on that answer).

import Base
import ../../bend/approvals.bend as Am
import ../../bend/tools.bend as Tl
import ../../laws/approvals/route.bend as Approvals
import ../base/logic/logic.bend as LLogicLogic

def po.outside(w: Bool, +es: List<&2, Nat>, +ds: List<&2, Am.Desk>, h: {w == False{} : Bool}) -> {Am.gate.by(w, es, ds) == Am.routed(es, Am.route(ds)) : Am.Gated}:
  match w:
    case True{}:
      LLogicLogic.approvals.pa.absurdF({Am.gate.by(True{}, es, ds) == Am.routed(es, Am.route(ds)) : Am.Gated}, Equal.sym(Bool, True{}, False{}, h))
    case False{}:
      {==}

def Approvals.approvals_outside_is_routed(auto, es, ds, outside):
  po.outside(Tl.within(es, auto), es, ds, outside)
