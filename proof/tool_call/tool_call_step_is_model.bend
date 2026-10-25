# eukhe: the proof of LAW tool_call_step_is_model
# The stepper opens taking reports (LA.tp.opened); from there every reply
# is S2's (LA.tp.taking, LA.tp.over), by induction on the events.

import Base
import ../../bend/tool_call.bend as Tc
import ../../bend/ffi_tool_call.bend as FTc
import ../../laws/tool_call.bend as ToolCall
import ./base.bend as LA

def ToolCall.tool_call_step_is_model(first, es):
  Equal.sym(List<&2, String>, ToolCall.tc_spec(es, False{}), ToolCall.tc_replies(es, ToolCall.tc_opened(first)), LA.tp.model(first, es))
