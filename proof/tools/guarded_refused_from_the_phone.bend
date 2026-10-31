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

# the hypothesis copies: the equality is about a data Bool, so both
# lemmas below get their own
def pa.dup(b: Bool, h: {b == True{} : Bool}) -> ({b == True{} : Bool} & {b == True{} : Bool}):
  match b:
    case True{}:
      ({==}, {==})
    case False{}:
      LLogicLogic.approvals.pa.absurdF(({False{} == True{} : Bool} & {False{} == True{} : Bool}), h)

def pa.use(+auto: List<&2, Nat>, +es: List<&2, Nat>, +above: List<&2, Am.Desk>, off: {Tl.elem(auto, 5n) == False{} : Bool}, one: ({Tl.elem(es, 5n) == True{} : Bool} & {Tl.elem(es, 5n) == True{} : Bool})) -> {Am.gate(auto, es, Am.Phone{} <> above) == Am.Routed{Am.Out{Nil{}, Am.Ruled{0n}}, Am.GatewayRefused{}} : Am.Gated}:
  match one:
    case (+has5, +guard5):
      LA.pa.phone_gate(auto, es, above, Am.GatewayRefused{}, LA.ps.auto_needs_every_effect(Tl.Step{0n, es}, auto, 5n, has5, off), pa.guard_true(Tl.elem(es, 5n), guard5))

def pa.guarded_from_phone(+auto: List<&2, Nat>, +es: List<&2, Nat>, protected: {Tl.elem(es, 5n) == True{} : Bool}, off: {Tl.elem(auto, 5n) == False{} : Bool}, +above: List<&2, Am.Desk>) -> {Am.gate(auto, es, Am.Phone{} <> above) == Am.Routed{Am.Out{Nil{}, Am.Ruled{0n}}, Am.GatewayRefused{}} : Am.Gated}:
  pa.use(auto, es, above, off, pa.dup(Tl.elem(es, 5n), protected))

def Tools.guarded_refused_from_the_phone(auto, es, protected, off, above):
  pa.guarded_from_phone(auto, es, protected, off, above)
