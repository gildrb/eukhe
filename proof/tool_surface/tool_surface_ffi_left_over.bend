# eukhe: the proof of LAW tool_surface_ffi_left_over
# The entry's decoder reads the request back with the input after it;
# that input is not empty, so the request is not the whole input
# (Wr.end is String.is_empty).

import Base
import ../../bend/ffi_tool_surface.bend as FTs
import ../../bend/wire.bend as Wr
import ../../laws/tool_surface.bend as ToolSurface
import ./base.bend as LATs

def ToolSurface.tool_surface_ffi_left_over(q, more, fits, some):
  %Equal.sym(Wr.Dec<FTs.Req>, FTs.get_req(ToolSurface.spell_req(q, more)), Wr.Got{q, more}, LATs.ts.rt(q, more, fits)) : {FTs.run(_) == ToolSurface.malformed() : String}
  %Equal.sym(Bool, String.is_empty(more), False{}, some) : {FTs.run.end(_, q) == ToolSurface.malformed() : String}
  {==}
