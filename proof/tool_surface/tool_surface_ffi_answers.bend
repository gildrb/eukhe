# eukhe: the proof of LAW tool_surface_ffi_answers
# The entry's decoder reads back the request Rust writes (LATs.ts.rt);
# nothing is left, so the entry answers the model's decision, spelled as
# the laws spell it (LATs.ts.reply).

import Base
import ../../bend/ffi_tool_surface.bend as FTs
import ../../bend/wire.bend as Wr
import ../../laws/tool_surface.bend as ToolSurface
import ./base.bend as LATs

def ToolSurface.tool_surface_ffi_answers(q, fits):
  %Equal.sym(Wr.Dec<FTs.Req>, FTs.get_req(ToolSurface.spell_req(q, "")), Wr.Got{q, ""}, LATs.ts.rt(q, "", fits)) : {FTs.run(_) == ToolSurface.spell_answer(q) : String}
  LATs.ts.reply(q)
