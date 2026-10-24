# eukhe: the proof of LAW guarded_refused_from_the_phone

import Base
import ../../bend/approvals.bend as Am
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

def pa.guard_true(b: Bool, h: {b == True{} : Bool}) -> {Am.guard(b) == Am.GatewayRefused{} : Am.Fate}:
  match b:
    case True{}:
      {==}
    case False{}:
      LLogicLogic.approvals.pa.absurdF({Am.guard(False{}) == Am.GatewayRefused{} : Am.Fate}, h)

# a disjunction whose right side holds
def pa.or_right(a: Bool, +b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

def pa.guarded_from_phone(+auto: List<&2, Nat>, +es: List<&2, Nat>, +secret: {Tl.elem(es, 6n) == True{} : Bool}, +above: List<&2, Am.Desk>) -> {Am.gate(auto, es, Am.Phone{} <> above) == Am.Routed{Am.Out{Nil{}, Am.Ruled{0n}}, Am.GatewayRefused{}} : Am.Gated}:
  LA.pa.phone_gate(auto, es, above, Am.GatewayRefused{}, LA.ps.auto_never_sensitive(Tl.Step{0n, es}, auto, 6n, secret, {==}), pa.guard_true(Bool.or(Tl.elem(es, 5n), Tl.elem(es, 6n)), pa.or_right(Tl.elem(es, 5n), Tl.elem(es, 6n), secret)))

def Tools.guarded_refused_from_the_phone(auto, es, secret, above):
  pa.guarded_from_phone(auto, es, secret, above)
