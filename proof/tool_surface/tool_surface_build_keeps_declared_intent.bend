# eukhe: the proof of LAW tool_surface_build_keeps_declared_intent
# The intent is an element of the declared parameters (LATs.ts.elem_at),
# so the model adds nothing.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tool_surface.bend as ToolSurface
import ./base.bend as LATs

def ToolSurface.tool_surface_build_keeps_declared_intent(pre, post, v):
  %Equal.sym(Bool, Tl.elem(List.append(&2, Nat, pre, 0n <> post), 0n), True{}, LATs.ts.elem_at(pre, 0n, post)) : {Tl.add_intent(_, List.append(&2, Nat, pre, 0n <> post)) == List.append(&2, Nat, pre, 0n <> post) : List<&2, Nat>}
  {==}
