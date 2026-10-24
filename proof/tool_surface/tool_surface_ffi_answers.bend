# eukhe: the proof of LAW tool_surface_ffi_answers
# The entry answers as the laws spell; the reader reads back the request
# Rust writes.

import Base
import ../../bend/ffi_tool_surface.bend as FTs
import ../../bend/wire.bend as Wr
import ../../laws/tool_surface.bend as ToolSurface
import ./base.bend as LATs

def ToolSurface.tool_surface_ffi_answers(q, fits):
  %Equal.sym(String, FTs.ffi(ToolSurface.spell_req(q, "")), ToolSurface.spec(ToolSurface.spell_req(q, "")), LATs.ts.exact(ToolSurface.spell_req(q, ""))) : {_ == ToolSurface.spell_answer(q) : String}
  %Equal.sym(Wr.Dec<FTs.Req>, ToolSurface.read_req(ToolSurface.spell_req(q, "")), Wr.Got{q, ""}, LATs.ts.rt(q, "", fits)) : {ToolSurface.spec.run(_) == ToolSurface.spell_answer(q) : String}
  {==}
