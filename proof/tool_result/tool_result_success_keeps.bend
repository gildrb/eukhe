# eukhe: the proof of LAW tool_result_success_keeps
#
# PROOF: the blocks sent are the spec's (tool_result_spec); the spec sends
# each block of a successful result as it is (tsk.go, by induction).

import Base
import ../../bend/tool_result.bend as Tr
import ../../spec/harness/tool_result.bend as S
import ../../laws/tool_result.bend as ToolResult
import ./tool_result_spec.bend as PToolResultSpec

def tsk.go(bs: List<&2, Tr.Blk>) -> {S.sent(False{}, bs) == bs : List<&2, Tr.Blk>}:
  match bs:
    case Nil{}:
      {==}
    case b <> +t:
      match b:
        case Tr.Txt{+s}:
          %Equal.sym(List<&2, Tr.Blk>, S.sent(False{}, t), t, tsk.go(t)) : {Tr.Txt{s} <> _ == Tr.Txt{s} <> t : List<&2, Tr.Blk>}
          {==}
        case Tr.Pic{+i}:
          %Equal.sym(List<&2, Tr.Blk>, S.sent(False{}, t), t, tsk.go(t)) : {Tr.Pic{i} <> _ == Tr.Pic{i} <> t : List<&2, Tr.Blk>}
          {==}

def ToolResult.tool_result_success_keeps(bs):
  %Equal.sym(List<&2, Tr.Blk>, Tr.sent(False{}, bs), S.sent(False{}, bs), ToolResult.tool_result_spec(False{}, bs)) : {_ == bs : List<&2, Tr.Blk>}
  tsk.go(bs)
