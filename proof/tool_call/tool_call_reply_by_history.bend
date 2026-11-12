# eukhe: the proof of LAW tool_call_reply_by_history
# The stepper opens taking reports (LA.tp.opened); after the events pre it
# holds a call ended exactly when an end is among them (LA.tp.fed_taking);
# the next event is then answered as S2 asks (LA.tp.answer).

import Base
import ../../bend/tool_call.bend as Tc
import ../../bend/ffi_tool_call.bend as FTc
import ../../laws/tool_call.bend as ToolCall
import ./base.bend as LA

def ToolCall.tool_call_reply_by_history(first, pre, e):
  %LA.tp.opened(first) : {ToolCall.tc_reply(FTc.step(ToolCall.tc_fed(pre, _), ToolCall.tc_spell(e))) == ToolCall.tc_answer(ToolCall.tc_ends(pre), e) : String}
  %Equal.sym(FTc.St, ToolCall.tc_fed(pre, FTc.Call{Tc.Taking{}}), FTc.Call{LA.tp.cof(ToolCall.tc_ends(pre))}, LA.tp.fed_taking(pre)) : {ToolCall.tc_reply(FTc.step(_, ToolCall.tc_spell(e))) == ToolCall.tc_answer(ToolCall.tc_ends(pre), e) : String}
  LA.tp.answer(ToolCall.tc_ends(pre), e)
