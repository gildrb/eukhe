# eukhe: the proof of LAW tool_surface_build_adds_at_most_one
# By cases on the model's test of the intent: the declared parameters as
# they are (nothing put before them), or the intent put before them.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tool_surface.bend as ToolSurface

def tsb.pick(b: Bool, +ps: List<&2, Nat>) -> Sigma<&1, &1, List<&2, Nat>, pre => {(Tl.add_intent(b, ps), Nat.is_le(List.length(&2, Nat, pre), 1n)) == (List.append(&2, Nat, pre, ps), True{}) : List<&2, Nat> & Bool}>:
  match b:
    case True{}:
      (Nil{}, {==})
    case False{}:
      ([0n], {==})

def ToolSurface.tool_surface_build_adds_at_most_one(ps, v):
  tsb.pick(Tl.elem(ps, Tl.intent()), ps)
