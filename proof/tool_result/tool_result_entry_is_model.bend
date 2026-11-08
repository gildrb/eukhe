# eukhe: the proof of LAW tool_result_entry_is_model
#
# PROOF: the spelled request reads back whole with nothing left
# (tool_result_entry_reads), so the entry answers the model's plan,
# encoded as the spec spells it (LA.trb.outs).

import Base
import ../../bend/tool_result.bend as Tr
import ../../bend/ffi_tool_result.bend as FTr
import ../../bend/wire.bend as Wr
import ../../laws/tool_result.bend as ToolResult
import ./base.bend as LA
import ./tool_result_entry_reads.bend as PToolResultEntryReads

def trm.reply(q: FTr.Req) -> {FTr.answer(q) == ToolResult.sp_w_reply(q) : String}:
  match q:
    case FTr.Req{+e, +ks}:
      LA.trb.outs(Tr.plan(e, ks), "")

def ToolResult.tool_result_entry_is_model(q, h):
  %Equal.sym(Wr.Dec<FTr.Req>, FTr.get_req(ToolResult.sp_w_req(q, "")), Wr.Got{q, ""}, ToolResult.tool_result_entry_reads(q, "", h)) : {FTr.ffi.got(_) == ToolResult.sp_w_reply(q) : String}
  trm.reply(q)
