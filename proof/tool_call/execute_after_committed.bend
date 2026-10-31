# eukhe: the proof of LAW execute_after_committed
# Every history from w0 is a shape (LA.ep.from_w0); no shape holds an
# early run (LA.ep.early).

import Base
import ../../bend/tool_call.bend as Tc
import ../../bend/ffi_tool_call.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/tool_call.bend as ToolCall
import ../../spec/harness/effect.bend as Sp
import ./base.bend as LA

def ToolCall.execute_after_committed(es):
  Equal.trans(Nat, Sp.early(ToolCall.ef_run(es, Sp.w0())), Sp.early(LA.embed(LA.shrun(es, LA.ShA{}))), 0n, Equal.cong(Sp.World, Nat, w => Sp.early(w), ToolCall.ef_run(es, Sp.w0()), LA.embed(LA.shrun(es, LA.ShA{})), LA.ep.from_w0(es)), LA.ep.early(LA.shrun(es, LA.ShA{})))
