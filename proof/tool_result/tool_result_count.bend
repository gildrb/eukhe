# eukhe: the proof of LAW tool_result_count
#
# PROOF: the blocks sent are the spec's (tool_result_spec), which sends
# one block per block (tc.go, by induction).

import Base
import ../../bend/tool_result.bend as Tr
import ../../spec/harness/tool_result.bend as S
import ../../laws/tool_result.bend as ToolResult
import ./tool_result_spec.bend as PToolResultSpec

def tc.go(+err: Bool, bs: List<&2, Tr.Blk>) -> {List.length(&2, Tr.Blk, S.sent(err, bs)) == List.length(&2, Tr.Blk, bs) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case b <> +t:
      %Equal.sym(Nat, List.length(&2, Tr.Blk, S.sent(err, t)), List.length(&2, Tr.Blk, t), tc.go(err, t)) : {1n+_ == 1n+List.length(&2, Tr.Blk, t) : Nat}
      {==}

def ToolResult.tool_result_count(err, bs):
  %Equal.sym(List<&2, Tr.Blk>, Tr.sent(err, bs), S.sent(err, bs), ToolResult.tool_result_spec(err, bs)) : {List.length(&2, Tr.Blk, _) == List.length(&2, Tr.Blk, bs) : Nat}
  tc.go(err, bs)
