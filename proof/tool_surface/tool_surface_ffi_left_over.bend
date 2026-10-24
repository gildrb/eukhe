# eukhe: the proof of LAW tool_surface_ffi_left_over
# The reader reads the request back with the input after it; that input
# is not empty, so the request is not the whole input (wire_end_exact).

import Base
import ../../bend/ffi_tool_surface.bend as FTs
import ../../bend/wire.bend as Wr
import ../../laws/tool_surface.bend as ToolSurface
import ../../laws/wire.bend as Wire
import ../wire/wire_end_exact.bend as PWireEndExact
import ./base.bend as LATs

def ToolSurface.tool_surface_ffi_left_over(q, more, fits, some):
  %Equal.sym(String, FTs.ffi(ToolSurface.spell_req(q, more)), ToolSurface.spec(ToolSurface.spell_req(q, more)), LATs.ts.exact(ToolSurface.spell_req(q, more))) : {_ == ToolSurface.malformed() : String}
  %Equal.sym(Wr.Dec<FTs.Req>, ToolSurface.read_req(ToolSurface.spell_req(q, more)), Wr.Got{q, more}, LATs.ts.rt(q, more, fits)) : {ToolSurface.spec.run(_) == ToolSurface.malformed() : String}
  %Equal.sym(Bool, Wr.end(more), String.is_empty(more), Wire.wire_end_exact(more)) : {ToolSurface.spec.end(_, q) == ToolSurface.malformed() : String}
  %Equal.sym(Bool, String.is_empty(more), False{}, some) : {ToolSurface.spec.end(_, q) == ToolSurface.malformed() : String}
  {==}
