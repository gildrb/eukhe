# eukhe: the proof of LAW gateway_refuses_protected

import Base
import ../../bend/approvals.bend as Am
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ../base/logic/logic.bend as LLogicLogic

# the guard refuses when the protected code is present
def pa.guard_true(b: Bool, h: {b == True{} : Bool}) -> {Am.guard(b) == Am.GatewayRefused{} : Am.Fate}:
  match b:
    case True{}:
      {==}
    case False{}:
      LLogicLogic.approvals.pa.absurdF({Am.guard(False{}) == Am.GatewayRefused{} : Am.Fate}, h)

def pa.refuses_protected(+es: List<&2, Nat>, protected: {Tl.elem(es, 5n) == True{} : Bool}, +above: List<&2, Am.Desk>) -> {Am.fate(es, Am.Out.end(Am.route(Am.Phone{} <> above))) == Am.GatewayRefused{} : Am.Fate}:
  pa.guard_true(Tl.elem(es, 5n), protected)

def Tools.gateway_refuses_protected(es, protected, above):
  pa.refuses_protected(es, protected, above)
