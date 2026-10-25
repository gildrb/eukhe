# eukhe: the proof of LAW tool_call_open_exact

import Base
import ../../bend/ffi_tool_call.bend as FTc
import ../../laws/tool_call.bend as ToolCall

def tc.open_exact(first: Bool) -> {ToolCall.tc_reply(FTc.open(ToolCall.tc_spell_open(first))) == ToolCall.tc_open_spec(first) : String}:
  match first:
    case True{}:
      {==}
    case False{}:
      {==}

def ToolCall.tool_call_open_exact(first):
  tc.open_exact(first)
