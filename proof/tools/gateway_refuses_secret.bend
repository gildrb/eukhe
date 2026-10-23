# eukhe: the proof of LAW gateway_refuses_secret

import Base
import ../../bend/approvals.bend as Am
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ../base/logic/logic.bend as LLogicLogic

# and when its second part holds
def pa.guard_second(b1: Bool, b2: Bool, h: {b2 == True{} : Bool}) -> {Am.guard(Bool.or(b1, b2)) == Am.GatewayRefused{} : Am.Fate}:
  match b1:
    case True{}:
      {==}
    case False{}:
      match b2:
        case True{}:
          {==}
        case False{}:
          LLogicLogic.approvals.pa.absurdF({Am.guard(Bool.or(False{}, False{})) == Am.GatewayRefused{} : Am.Fate}, h)

def pa.refuses_secret(+es: List<&2, Nat>, secret: {Tl.elem(es, 6n) == True{} : Bool}, +above: List<&2, Am.Desk>) -> {Am.fate(es, Am.Out.end(Am.route(Am.Phone{} <> above))) == Am.GatewayRefused{} : Am.Fate}:
  pa.guard_second(Tl.elem(es, 5n), Tl.elem(es, 6n), secret)

def Tools.gateway_refuses_secret(es, secret, above):
  pa.refuses_secret(es, secret, above)
