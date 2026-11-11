# eukhe: the proof of LAW tool_result_plan_success_image
#
# PROOF: induction on the blocks before it: with no block before it, the
# image of a successful result is answered Keep; each block before it is
# answered alone, so its answer leads both sides.

import Base
import ../../bend/tool_result.bend as Tr
import ../../spec/harness/tool_result.bend as S
import ../../laws/tool_result.bend as ToolResult

def ToolResult.tool_result_plan_success_image(pre, post):
  match pre:
    case Nil{}:
      {==}
    case i <> t:
      Equal.cong(List<&2, Tr.Out>, List<&2, Tr.Out>, z => Tr.plan.one(i, False{}) <> z, Tr.plan(False{}, List.append(&2, Bool, t, True{} <> post)), List.append(&2, Tr.Out, Tr.plan(False{}, t), Tr.Keep{} <> Tr.plan(False{}, post)), ToolResult.tool_result_plan_success_image(t, post))
