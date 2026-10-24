# eukhe: the proof of LAW tool_surface_ffi_exact
# The entry reads every input as the laws' reader does and answers what
# the laws spell (LATs.ts.exact).

import Base
import ../../laws/tool_surface.bend as ToolSurface
import ./base.bend as LATs

def ToolSurface.tool_surface_ffi_exact(s):
  LATs.ts.exact(s)
