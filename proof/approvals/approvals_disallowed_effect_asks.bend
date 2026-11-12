# eukhe: the proof of LAW approvals_disallowed_effect_asks
# PROOF: the gate first asks whether the step is within the auto set; an
# effect the auto set does not run unasked makes it not, wherever it sits
# (LG.gd.within_no, by induction on pre), so the step is routed.

import Base
import ../../bend/approvals.bend as Am
import ../../bend/tools.bend as Tl
import ../../laws/approvals/route.bend as Approvals
import ./base/gate.bend as LG

def Approvals.approvals_disallowed_effect_asks(auto, pre, x, post, ds, no):
  +ES = List.append(&2, Nat, pre, x <> post)
  %Equal.sym(Bool, Tl.within(ES, auto), False{}, LG.gd.within_no(pre, x, post, auto, no)) : {Am.gate.by(_, ES, ds) == Am.Routed{Am.route(ds), Am.fate(ES, Am.Out.end(Am.route(ds)))} : Am.Gated}
  {==}
