# eukhe: the proof of LAW tool_surface_quit_spec
# Tl.drop keeps or drops each item as the spec does (tsq.go), item by item.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tool_surface.bend as ToolSurface

def tsq.go(b: Bool, y: Nat, rest: List<&2, Nat>, +t: Nat, ih: {Tl.drop(rest, t) == ToolSurface.ts_without(rest, t) : List<&2, Nat>}) -> {Tl.drop.go(y <> rest, t, b) == ToolSurface.ts_without.keep(b, y, ToolSurface.ts_without(rest, t)) : List<&2, Nat>}:
  match b:
    case True{}:
      ih
    case False{}:
      %ih : {y <> Tl.drop(rest, t) == y <> _ : List<&2, Nat>}
      {==}

def tsq.drop(xs: List<&2, Nat>, +t: Nat) -> {Tl.drop(xs, t) == ToolSurface.ts_without(xs, t) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +rest:
      tsq.go(Nat.is_eq(y, t), y, rest, t, tsq.drop(rest, t))

def ToolSurface.tool_surface_quit_spec(r, d, x, t):
  tsq.drop(d, t)
