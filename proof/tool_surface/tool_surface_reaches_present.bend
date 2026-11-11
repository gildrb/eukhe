# eukhe: the proof of LAW tool_surface_reaches_present
# The tool is an element of the dynamic tools (LATs.ts.elem_at).

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tool_surface.bend as ToolSurface
import ./base.bend as LATs

def ToolSurface.tool_surface_reaches_present(r, pre, t, post, x):
  LATs.ts.elem_at(pre, t, post)
