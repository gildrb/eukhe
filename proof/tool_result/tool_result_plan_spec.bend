# eukhe: the proof of LAW tool_result_plan_spec
#
# PROOF: induction on the blocks' kinds: the code's answer for one block
# is the spec's (trps.one, both flags and both kinds); the rest by
# induction.

import Base
import ../../bend/tool_result.bend as Tr
import ../../spec/harness/tool_result.bend as S
import ../../laws/tool_result.bend as ToolResult

# one block's answer is the spec's
def trps.one(img: Bool, err: Bool) -> {Tr.plan.one(img, err) == S.answer(err, img) : Tr.Out}:
  match img:
    case True{}:
      match err:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match err:
        case True{}:
          {==}
        case False{}:
          {==}

def ToolResult.tool_result_plan_spec(err, ks):
  match ks:
    case Nil{}:
      {==}
    case +i <> +t:
      %ToolResult.tool_result_plan_spec(err, t) : {Tr.plan.one(i, err) <> Tr.plan(err, t) == S.answer(err, i) <> _ : List<&2, Tr.Out>}
      %trps.one(i, err) : {Tr.plan.one(i, err) <> Tr.plan(err, t) == _ <> Tr.plan(err, t) : List<&2, Tr.Out>}
      {==}
