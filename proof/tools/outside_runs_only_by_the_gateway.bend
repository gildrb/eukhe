# eukhe: the proof of LAW outside_runs_only_by_the_gateway

import Base
import ../../bend/approvals.bend as Am
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ./base.bend as LA

def pa.outside_by_gateway(+auto: List<&2, Nat>, +es: List<&2, Nat>, outside: {Tl.elem(es, 4n) == True{} : Bool}, not_protected: {Tl.elem(es, 5n) == False{} : Bool}, not_secret: {Tl.elem(es, 6n) == False{} : Bool}, +above: List<&2, Am.Desk>) -> {Am.gate(auto, es, Am.Phone{} <> above) == Am.Routed{Am.Out{Nil{}, Am.Ruled{0n}}, Am.Runs{}} : Am.Gated}:
  LA.pa.phone_gate(auto, es, above, Am.Runs{}, LA.ps.auto_never_sensitive(Tl.Step{0n, es}, auto, 4n, outside, {==}), LA.pa.guard_neither(Tl.elem(es, 5n), Tl.elem(es, 6n), not_protected, not_secret))

def Tools.outside_runs_only_by_the_gateway(auto, es, outside, not_protected, not_secret, above):
  pa.outside_by_gateway(auto, es, outside, not_protected, not_secret, above)
