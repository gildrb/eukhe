# eukhe: the proof of LAW tool_result_error_text_only
#
# PROOF: the blocks sent are the spec's (tool_result_spec); the spec sends
# each block of an error result as a text block (tet.go, by induction).

import Base
import ../../bend/tool_result.bend as Tr
import ../../spec/harness/tool_result.bend as S
import ../../laws/tool_result.bend as ToolResult
import ./tool_result_spec.bend as PToolResultSpec

def tet.go(bs: List<&2, Tr.Blk>) -> {S.all_text(S.sent(True{}, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case b <> t:
      match b:
        case Tr.Txt{s}:
          tet.go(t)
        case Tr.Pic{i}:
          tet.go(t)

def ToolResult.tool_result_error_text_only(bs):
  %Equal.sym(List<&2, Tr.Blk>, Tr.sent(True{}, bs), S.sent(True{}, bs), ToolResult.tool_result_spec(True{}, bs)) : {S.all_text(_) == True{} : Bool}
  tet.go(bs)
