# eukhe: the proof of LAW tool_result_entry_spec
#
# PROOF: the entry answers the model's plan, spelled
# (tool_result_entry_is_model); that plan is the spec's
# (tool_result_plan_spec) and has one answer per block
# (tool_result_plan_one_each), so the spelling is the spec's (tres.reply).

import Base
import ../../bend/tool_result.bend as Tr
import ../../bend/ffi_tool_result.bend as FTr
import ../../bend/wire.bend as Wr
import ../../spec/harness/tool_result.bend as S
import ../../laws/tool_result.bend as ToolResult
import ./tool_result_entry_is_model.bend as PToolResultEntryIsModel
import ./tool_result_plan_spec.bend as PToolResultPlanSpec
import ./tool_result_plan_one_each.bend as PToolResultPlanOneEach

# the model's reply is the spec's
def tres.reply(q: FTr.Req) -> {ToolResult.sp_w_reply(q) == ToolResult.sp_w_spec_reply(q) : String}:
  match q:
    case FTr.Req{+e, +ks}:
      %ToolResult.tool_result_plan_spec(e, ks) : {Wr.put_nat(List.length(&2, Tr.Out, Tr.plan(e, ks)), ToolResult.sp_w_outs(Tr.plan(e, ks), "")) == Wr.put_nat(List.length(&2, Bool, ks), ToolResult.sp_w_outs(_, "")) : String}
      %ToolResult.tool_result_plan_one_each(e, ks) : {Wr.put_nat(List.length(&2, Tr.Out, Tr.plan(e, ks)), ToolResult.sp_w_outs(Tr.plan(e, ks), "")) == Wr.put_nat(_, ToolResult.sp_w_outs(Tr.plan(e, ks), "")) : String}
      {==}

def ToolResult.tool_result_entry_spec(q, h):
  Equal.trans(String, FTr.ffi(ToolResult.sp_w_req(q, "")), ToolResult.sp_w_reply(q), ToolResult.sp_w_spec_reply(q), ToolResult.tool_result_entry_is_model(q, h), tres.reply(q))
