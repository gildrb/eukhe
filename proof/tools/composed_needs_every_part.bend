# eukhe: the proof of LAW composed_needs_every_part

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ./base.bend as LA

def ps.composed_needs_every_part(+i: Nat, +pre: List<&2, List<&2, Nat>>, +p: List<&2, Nat>, +post: List<&2, List<&2, Nat>>, +auto: List<&2, Nat>, +c: Nat, has: {Tl.elem(p, c) == True{} : Bool}, out: {Bool.and(Tl.grantable(c), Tl.elem(auto, c)) == False{} : Bool}) -> {Tl.auto.at(auto, Tl.Step{i, Tl.join(List.append(&2, List<&2, Nat>, pre, p <> post))}) == False{} : Bool}:
  LA.ps.within_out(Tl.join(List.append(&2, List<&2, Nat>, pre, p <> post)), auto, c, LA.ps.step_holds_every_part(pre, p, post, c, has), out)

def Tools.composed_needs_every_part(i, pre, p, post, auto, c, has, out):
  ps.composed_needs_every_part(i, pre, p, post, auto, c, has, out)
