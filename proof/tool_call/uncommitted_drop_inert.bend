# eukhe: the proof of LAW uncommitted_drop_inert
# Every history from w0 is a shape (LA.ep.from_w0); without a commit
# that shape is w0's (LA.ep.inert).

import Base
import ../../bend/tool_call.bend as Tc
import ../../bend/ffi_tool_call.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/tool_call.bend as ToolCall
import ../../spec/harness/effect.bend as Sp
import ./base.bend as LA

def ToolCall.uncommitted_drop_inert(es, no):
  %Equal.sym(Sp.World, ToolCall.ef_run(es, Sp.w0()), LA.embed(LA.shrun(es, LA.ShA{})), LA.ep.from_w0(es)) : {_ == Sp.w0() : Sp.World}
  %Equal.sym(LA.Shape, LA.shrun(es, LA.ShA{}), LA.ShA{}, LA.ep.inert(es, no)) : {LA.embed(_) == Sp.w0() : Sp.World}
  {==}
