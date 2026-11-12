# eukhe: the proof of LAW tool_surface_build_version
# Nat.max(v, 1n) computes on 0, 1 and 2 + k.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tool_surface.bend as ToolSurface

def ToolSurface.tool_surface_build_version(ps, w):
  match w:
    case 0n:
      {==}
    case 1n+k:
      {==}
