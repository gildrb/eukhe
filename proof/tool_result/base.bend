# eukhe: lemmas shared by the proofs of area tool_result: the spec's
# blocks of a list split at any point; the entry's encoders are the spec's
# spellings (a list of Bools, a plan)

import Base
import ../../bend/tool_result.bend as Tr
import ../../bend/ffi_tool_result.bend as FTr
import ../../bend/wire.bend as Wr
import ../../spec/harness/tool_result.bend as S
import ../../laws/tool_result.bend as ToolResult
import ../log/base.bend as LLog

# Blocks
# ------

# the spec sends a list split in two as the two halves, in order
def trb.append(+err: Bool, xs: List<&2, Tr.Blk>, +ys: List<&2, Tr.Blk>) -> {S.sent(err, List.append(&2, Tr.Blk, xs, ys)) == List.append(&2, Tr.Blk, S.sent(err, xs), S.sent(err, ys)) : List<&2, Tr.Blk>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(List<&2, Tr.Blk>, S.sent(err, List.append(&2, Tr.Blk, t, ys)), List.append(&2, Tr.Blk, S.sent(err, t), S.sent(err, ys)), trb.append(err, t, ys)) : {S.block(err, x) <> _ == S.block(err, x) <> List.append(&2, Tr.Blk, S.sent(err, t), S.sent(err, ys)) : List<&2, Tr.Blk>}
      {==}

# Wire
# ----

# the log area's spelling of Bool items is the spec's
def trb.bools(xs: List<&2, Bool>, rest: String) -> {LLog.pe.bools(xs, rest) == ToolResult.sp_w_bools(xs, rest) : String}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(String, LLog.pe.bools(t, rest), ToolResult.sp_w_bools(t, rest), trb.bools(t, rest)) : {Wr.put_bool(x, _) == Wr.put_bool(x, ToolResult.sp_w_bools(t, rest)) : String}
      {==}

# a list of Bools is spelled by the spec
def trb.put_list(+xs: List<&2, Bool>, rest: String) -> {Wr.put_list(~Bool, ~Wr.put_bool, xs, rest) == Wr.put_nat(List.length(&2, Bool, xs), ToolResult.sp_w_bools(xs, rest)) : String}:
  %trb.bools(xs, rest) : {Wr.put_list(~Bool, ~Wr.put_bool, xs, rest) == Wr.put_nat(List.length(&2, Bool, xs), _) : String}
  LLog.pe.put_list(xs, rest)

# the item loop of a plan: its count, and the spec's spelling of its items
def trb.outs_go(os: List<&2, Tr.Out>, -rest: String) -> {Wr.put_list.go(~Tr.Out, ~FTr.put_out, os, rest) == (List.length(&2, Tr.Out, os), ToolResult.sp_w_outs(os, rest)) : Nat & String}:
  match os:
    case Nil{}:
      {==}
    case o <> +t:
      match o:
        case Tr.Keep{}:
          %Equal.sym(Nat & String, Wr.put_list.go(~Tr.Out, ~FTr.put_out, t, rest), (List.length(&2, Tr.Out, t), ToolResult.sp_w_outs(t, rest)), trb.outs_go(t, rest)) : {Wr.put_list.step(~Tr.Out, ~FTr.put_out, Tr.Keep{}, _) == (1n+List.length(&2, Tr.Out, t), Wr.put_nat(0n, ToolResult.sp_w_outs(t, rest))) : Nat & String}
          {==}
        case Tr.Omit{+l}:
          %Equal.sym(Nat & String, Wr.put_list.go(~Tr.Out, ~FTr.put_out, t, rest), (List.length(&2, Tr.Out, t), ToolResult.sp_w_outs(t, rest)), trb.outs_go(t, rest)) : {Wr.put_list.step(~Tr.Out, ~FTr.put_out, Tr.Omit{l}, _) == (1n+List.length(&2, Tr.Out, t), Wr.put_nat(1n, Wr.put_str(l, ToolResult.sp_w_outs(t, rest)))) : Nat & String}
          {==}

# a plan is spelled by the spec: its count, then its items
def trb.outs(+os: List<&2, Tr.Out>, -rest: String) -> {Wr.put_list(~Tr.Out, ~FTr.put_out, os, rest) == Wr.put_nat(List.length(&2, Tr.Out, os), ToolResult.sp_w_outs(os, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Tr.Out, ~FTr.put_out, os, rest), (List.length(&2, Tr.Out, os), ToolResult.sp_w_outs(os, rest)), trb.outs_go(os, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Tr.Out, os), ToolResult.sp_w_outs(os, rest)) : String}
  {==}
