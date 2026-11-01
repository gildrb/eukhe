# eukhe: the proof of LAW tool_result_spec
#
# PROOF: induction on the blocks: the plan answers a text block Keep and
# an image block the line when the result is an error, else Keep (trs.pic),
# so each block applied is the spec's block; the rest by induction.

import Base
import ../../bend/tool_result.bend as Tr
import ../../spec/harness/tool_result.bend as S
import ../../laws/tool_result.bend as ToolResult

# an image applied with its answer is the spec's block
def trs.pic(err: Bool, +i: Nat) -> {Tr.apply.one(Tr.Pic{i}, Tr.plan.one(True{}, err)) == S.block(err, Tr.Pic{i}) : Tr.Blk}:
  match err:
    case True{}:
      {==}
    case False{}:
      {==}

def trs.go(+err: Bool, bs: List<&2, Tr.Blk>) -> {Tr.apply(bs, Tr.plan(err, Tr.kinds(bs))) == S.sent(err, bs) : List<&2, Tr.Blk>}:
  match bs:
    case Nil{}:
      {==}
    case b <> +t:
      match b:
        case Tr.Txt{+s}:
          %Equal.sym(List<&2, Tr.Blk>, Tr.apply(t, Tr.plan(err, Tr.kinds(t))), S.sent(err, t), trs.go(err, t)) : {Tr.Txt{s} <> _ == Tr.Txt{s} <> S.sent(err, t) : List<&2, Tr.Blk>}
          {==}
        case Tr.Pic{+i}:
          %Equal.sym(List<&2, Tr.Blk>, Tr.apply(t, Tr.plan(err, Tr.kinds(t))), S.sent(err, t), trs.go(err, t)) : {Tr.apply.one(Tr.Pic{i}, Tr.plan.one(True{}, err)) <> _ == S.block(err, Tr.Pic{i}) <> S.sent(err, t) : List<&2, Tr.Blk>}
          %Equal.sym(Tr.Blk, Tr.apply.one(Tr.Pic{i}, Tr.plan.one(True{}, err)), S.block(err, Tr.Pic{i}), trs.pic(err, i)) : {_ <> S.sent(err, t) == S.block(err, Tr.Pic{i}) <> S.sent(err, t) : List<&2, Tr.Blk>}
          {==}

def ToolResult.tool_result_spec(err, bs):
  trs.go(err, bs)
