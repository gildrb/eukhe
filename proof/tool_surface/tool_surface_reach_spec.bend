# eukhe: the proof of LAW tool_surface_reach_spec
# Tl.elem is the spec's membership, item by item.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tool_surface.bend as ToolSurface

def tsr.has(xs: List<&2, Nat>, +x: Nat) -> {Tl.elem(xs, x) == ToolSurface.ts_has(xs, x) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case y <> rest:
      %tsr.has(rest, x) : {Bool.or(Nat.is_eq(y, x), Tl.elem(rest, x)) == Bool.or(Nat.is_eq(y, x), _) : Bool}
      {==}

def ToolSurface.tool_surface_reach_spec(r, d, x, t):
  tsr.has(d, t)
