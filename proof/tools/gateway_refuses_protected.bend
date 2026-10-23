# eukhe: the proof of LAW gateway_refuses_protected

import Base
import ../../bend/tools.bend as Tl
import ../../bend/approvals.bend as Am
import ../../LAWS.bend as Laws
import ../base.bend as L

# the guard refuses when its first part holds
def pa.guard_first(b1: Bool, b2: Bool, h: {b1 == True{} : Bool}) -> {Am.guard(Bool.or(b1, b2)) == Am.GatewayRefused{} : Am.Fate}:
  match b1:
    case True{}:
      {==}
    case False{}:
      L.approvals.pa.absurdF({Am.guard(Bool.or(False{}, b2)) == Am.GatewayRefused{} : Am.Fate}, h)

def pa.refuses_protected(+es: List<&2, Nat>, protected: {Tl.elem(es, 5n) == True{} : Bool}, +above: List<&2, Am.Desk>) -> {Am.fate(es, Am.Out.end(Am.route(Am.Phone{} <> above))) == Am.GatewayRefused{} : Am.Fate}:
  pa.guard_first(Tl.elem(es, 5n), Tl.elem(es, 6n), protected)

def Laws.gateway_refuses_protected(es, protected, above):
  pa.refuses_protected(es, protected, above)
