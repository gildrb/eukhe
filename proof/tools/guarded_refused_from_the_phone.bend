# eukhe: the proof of LAW guarded_refused_from_the_phone

import Base
import ../../bend/tools.bend as Tl
import ../../bend/approvals.bend as Am
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

# a guarded step is never within the auto set
def pa.guarded_not_within(+auto: List<&2, Nat>, +es: List<&2, Nat>, b1: Bool, e1: {Tl.elem(es, 5n) == b1 : Bool}, b2: Bool, e2: {Tl.elem(es, 6n) == b2 : Bool}, g: {Bool.or(b1, b2) == True{} : Bool}) -> {Tl.within(es, auto) == False{} : Bool}:
  match b1:
    case True{}:
      LA.ps.auto_never_sensitive(Tl.Step{0n, es}, auto, 5n, e1, {==})
    case False{}:
      match b2:
        case True{}:
          LA.ps.auto_never_sensitive(Tl.Step{0n, es}, auto, 6n, e2, {==})
        case False{}:
          L.approvals.pa.absurdF({Tl.within(es, auto) == False{} : Bool}, g)

def pa.guard_true(b: Bool, h: {b == True{} : Bool}) -> {Am.guard(b) == Am.GatewayRefused{} : Am.Fate}:
  match b:
    case True{}:
      {==}
    case False{}:
      L.approvals.pa.absurdF({Am.guard(False{}) == Am.GatewayRefused{} : Am.Fate}, h)

def pa.guarded_from_phone(+auto: List<&2, Nat>, +es: List<&2, Nat>, +guarded: {Bool.or(Tl.elem(es, 5n), Tl.elem(es, 6n)) == True{} : Bool}, +above: List<&2, Am.Desk>) -> {Am.gate(auto, es, Am.Phone{} <> above) == Am.Routed{Am.Out{Nil{}, Am.Ruled{0n}}, Am.GatewayRefused{}} : Am.Gated}:
  LA.pa.phone_gate(auto, es, above, Am.GatewayRefused{}, pa.guarded_not_within(auto, es, Tl.elem(es, 5n), {==}, Tl.elem(es, 6n), {==}, guarded), pa.guard_true(Bool.or(Tl.elem(es, 5n), Tl.elem(es, 6n)), guarded))

def Laws.guarded_refused_from_the_phone(auto, es, guarded, above):
  pa.guarded_from_phone(auto, es, guarded, above)
