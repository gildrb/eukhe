# eukhe: the proof of LAW effect_once
# Every history from w0 is a shape (LA.ep.from_w0); every shape ran at
# most once or recorded a safe intent (LA.ep.once).

import Base
import ../../bend/tool_call.bend as Tc
import ../../bend/ffi_tool_call.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/tool_call.bend as ToolCall
import ../../spec/harness/effect.bend as Sp
import ./base.bend as LA

def ToolCall.effect_once(es):
  Equal.trans(Bool, Bool.or(Sp.safe_intent(ToolCall.ef_run(es, Sp.w0())), Nat.is_le(Sp.effects(ToolCall.ef_run(es, Sp.w0())), 1n)), Bool.or(Sp.safe_intent(LA.embed(LA.shrun(es, LA.ShA{}))), Nat.is_le(Sp.effects(LA.embed(LA.shrun(es, LA.ShA{}))), 1n)), True{}, Equal.cong(Sp.World, Bool, +w => Bool.or(Sp.safe_intent(w), Nat.is_le(Sp.effects(w), 1n)), ToolCall.ef_run(es, Sp.w0()), LA.embed(LA.shrun(es, LA.ShA{})), LA.ep.from_w0(es)), LA.ep.once(LA.shrun(es, LA.ShA{})))
