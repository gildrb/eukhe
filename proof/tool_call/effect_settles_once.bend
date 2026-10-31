# eukhe: the proof of LAW effect_settles_once
# Every history from w0 is a shape (LA.ep.from_w0); every shape settled
# at most once (LA.ep.settles).

import Base
import ../../bend/tool_call.bend as Tc
import ../../bend/ffi_tool_call.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/tool_call.bend as ToolCall
import ../../spec/harness/effect.bend as Sp
import ./base.bend as LA

def ToolCall.effect_settles_once(es):
  Equal.trans(Bool, Nat.is_le(Sp.settles(ToolCall.ef_run(es, Sp.w0())), 1n), Nat.is_le(Sp.settles(LA.embed(LA.shrun(es, LA.ShA{}))), 1n), True{}, Equal.cong(Sp.World, Bool, w => Nat.is_le(Sp.settles(w), 1n), ToolCall.ef_run(es, Sp.w0()), LA.embed(LA.shrun(es, LA.ShA{})), LA.ep.from_w0(es)), LA.ep.settles(LA.shrun(es, LA.ShA{})))
