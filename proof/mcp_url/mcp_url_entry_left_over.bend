# eukhe: the proof of LAW mcp_url_entry_left_over
#
# PROOF: the spelled host reads back with the rest untouched (wire_str_round_trip); the rest is not empty, so the entry answers the error form.

import Base
import ../../bend/mcp_url.bend as Mu
import ../../bend/ffi_mcp_url.bend as FMu
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/mcp_url.bend as McpUrl
import ../base/wire.bend as LWire

def McpUrl.mcp_url_entry_left_over(h, c, t, fit):
  %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(h, SCon{c, t})), Wr.Got{h, SCon{c, t}}, Wire.wire_str_round_trip(h, SCon{c, t}, fit)) : {FMu.ffi.got(_) == Wr.err("mcp_url: malformed request") : String}
  {==}
