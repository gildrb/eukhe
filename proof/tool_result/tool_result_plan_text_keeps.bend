# eukhe: the proof of LAW tool_result_plan_text_keeps
#
# PROOF: induction on the blocks before it: with no block before it, a
# text block is answered Keep under both flags; each block before it is
# answered alone, so its answer leads both sides.

import Base
import ../../bend/tool_result.bend as Tr
import ../../spec/harness/tool_result.bend as S
import ../../laws/tool_result.bend as ToolResult

def ToolResult.tool_result_plan_text_keeps(err, pre, post):
  match pre:
    case Nil{}:
      {==}
    case i <> t:
      Equal.cong(List<&2, Tr.Out>, List<&2, Tr.Out>, z => Tr.plan.one(i, err) <> z, Tr.plan(err, List.append(&2, Bool, t, False{} <> post)), List.append(&2, Tr.Out, Tr.plan(err, t), Tr.Keep{} <> Tr.plan(err, post)), ToolResult.tool_result_plan_text_keeps(err, t, post))
