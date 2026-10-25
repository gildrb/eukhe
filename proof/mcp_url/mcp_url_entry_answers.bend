# eukhe: the proof of LAW mcp_url_entry_answers
#
# PROOF: the spelled host reads back whole with nothing left (wire_str_round_trip), so the entry answers the model's verdict, which is the spec's (mcp_url_spec).

import Base
import ../../bend/mcp_url.bend as Mu
import ../../bend/ffi_mcp_url.bend as FMu
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/mcp_url.bend as McpUrl
import ../base/wire.bend as LWire
import ./mcp_url_spec.bend as PMcpUrlSpec

def McpUrl.mcp_url_entry_answers(h, fit):
  %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(h, "")), Wr.Got{h, ""}, Wire.wire_str_round_trip(h, "", fit)) : {FMu.ffi.got(_) == McpUrl.mu_w_reply(h) : String}
  %McpUrl.mcp_url_spec(h) : {Wr.put_bool(Mu.refused(h), "") == Wr.put_bool(_, "") : String}
  {==}
