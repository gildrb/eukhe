# eukhe: the proof of LAW approvals_gateway_runs_unprotected
# PROOF: the gateway rule reads whether 5 is among the effects, the
# membership the laws' sp_has computes (LAD.ap.has); it is not, so the step
# runs.

import Base
import ../../bend/approvals.bend as Am
import ../../bend/tools.bend as Tl
import ../../laws/approvals/desk.bend as ApprovalsDesk
import ./base/desk.bend as LAD

def ApprovalsDesk.approvals_gateway_runs_unprotected(es, a, no):
  +e = Equal.trans(Bool, Tl.elem(es, 5n), ApprovalsDesk.sp_has(es, 5n), False{}, LAD.ap.has(es, 5n), no)
  %Equal.sym(Bool, Tl.elem(es, 5n), False{}, e) : {Am.guard(_) == Am.Runs{} : Am.Fate}
  {==}
