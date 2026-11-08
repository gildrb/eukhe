# eukhe: the proof of LAW tool_result_error_image_line
#
# PROOF: every blocks sent are the spec's (tool_result_spec); the spec
# sends a list split in two as the two halves (LA.trb.append), and the
# half that opens with the block sends Tr.Txt{S.line()} first.

import Base
import ../../bend/tool_result.bend as Tr
import ../../spec/harness/tool_result.bend as S
import ../../laws/tool_result.bend as ToolResult
import ./base.bend as LA
import ./tool_result_spec.bend as PToolResultSpec

def ToolResult.tool_result_error_image_line(pre, i, post):
  +whole = List.append(&2, Tr.Blk, pre, Tr.Pic{i} <> post)
  %Equal.sym(List<&2, Tr.Blk>, Tr.sent(True{}, whole), S.sent(True{}, whole), ToolResult.tool_result_spec(True{}, whole)) : {_ == List.append(&2, Tr.Blk, Tr.sent(True{}, pre), Tr.Txt{S.line()} <> Tr.sent(True{}, post)) : List<&2, Tr.Blk>}
  %Equal.sym(List<&2, Tr.Blk>, Tr.sent(True{}, pre), S.sent(True{}, pre), ToolResult.tool_result_spec(True{}, pre)) : {S.sent(True{}, whole) == List.append(&2, Tr.Blk, _, Tr.Txt{S.line()} <> Tr.sent(True{}, post)) : List<&2, Tr.Blk>}
  %Equal.sym(List<&2, Tr.Blk>, Tr.sent(True{}, post), S.sent(True{}, post), ToolResult.tool_result_spec(True{}, post)) : {S.sent(True{}, whole) == List.append(&2, Tr.Blk, S.sent(True{}, pre), Tr.Txt{S.line()} <> _) : List<&2, Tr.Blk>}
  LA.trb.append(True{}, pre, Tr.Pic{i} <> post)
