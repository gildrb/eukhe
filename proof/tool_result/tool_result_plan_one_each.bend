# eukhe: the proof of LAW tool_result_plan_one_each
#
# PROOF: induction on the blocks: one answer per block.

import Base
import ../../bend/tool_result.bend as Tr
import ../../laws/tool_result.bend as ToolResult

def ToolResult.tool_result_plan_one_each(err, ks):
  match ks:
    case Nil{}:
      {==}
    case k <> +t:
      %Equal.sym(Nat, List.length(&2, Tr.Out, Tr.plan(err, t)), List.length(&2, Bool, t), ToolResult.tool_result_plan_one_each(err, t)) : {1n+_ == 1n+List.length(&2, Bool, t) : Nat}
      {==}
