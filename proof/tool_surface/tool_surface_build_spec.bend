# eukhe: the proof of LAW tool_surface_build_spec
# Tl.elem is the spec's membership (tool_surface_reach_spec's tsr.has);
# Nat.max(v, 1n) is v, or 1 for 0, by cases.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tool_surface.bend as ToolSurface
import ./tool_surface_reach_spec.bend as PToolSurfaceReachSpec

def tsb.version(v: Nat) -> {Nat.max(v, 1n) == ToolSurface.ts_version(v) : Nat}:
  match v:
    case 0n:
      {==}
    case 1n+w:
      match w:
        case 0n:
          {==}
        case 1n+k:
          {==}

def tsb.pick(b: Bool, ps: List<&2, Nat>) -> {Tl.add_intent(b, ps) == ToolSurface.ts_params.pick(b, ps) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ToolSurface.tool_surface_build_spec(ps, v):
  %PToolSurfaceReachSpec.tsr.has(ps, 0n) : {Tl.build(Tl.Schema{ps, v}) == Tl.Schema{ToolSurface.ts_params.pick(_, ps), ToolSurface.ts_version(v)} : Tl.Schema}
  %tsb.version(v) : {Tl.build(Tl.Schema{ps, v}) == Tl.Schema{ToolSurface.ts_params.pick(Tl.elem(ps, 0n), ps), _} : Tl.Schema}
  %tsb.pick(Tl.elem(ps, 0n), ps) : {Tl.build(Tl.Schema{ps, v}) == Tl.Schema{_, Nat.max(v, 1n)} : Tl.Schema}
  {==}
