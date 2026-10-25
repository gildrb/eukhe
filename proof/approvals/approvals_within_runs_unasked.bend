# eukhe: the proof of LAW approvals_within_runs_unasked
# PROOF: the gate's first choice is whether the step is within the auto
# set; within, it is Unasked (a case on that answer).

import Base
import ../../bend/approvals.bend as Am
import ../../bend/tools.bend as Tl
import ../../laws/approvals/route.bend as Approvals
import ../base/logic/logic.bend as LLogicLogic

def pu.within(w: Bool, +es: List<&2, Nat>, +ds: List<&2, Am.Desk>, h: {w == True{} : Bool}) -> {Am.gate.by(w, es, ds) == Am.Unasked{} : Am.Gated}:
  match w:
    case True{}:
      {==}
    case False{}:
      LLogicLogic.pc.absurd_ft({Am.gate.by(False{}, es, ds) == Am.Unasked{} : Am.Gated}, h)

def Approvals.approvals_within_runs_unasked(auto, es, ds, within):
  pu.within(Tl.within(es, auto), es, ds, within)
