# eukhe: the proof of LAW stream_settles_once
# The replies are S2's (LA.tp.model): before the end none settles, the
# end settles, and nothing after it does (LA.tp.s_open, LA.tp.j_over).

import Base
import ../../laws/tool_call.bend as ToolCall
import ./base.bend as LA

def ToolCall.stream_settles_once(first, es):
  %LA.tp.model(first, es) : {List.length(&2, String, ToolCall.tc_journaled(_)) == ToolCall.tc_once(ToolCall.tc_ends(es)) : Nat}
  Equal.sym(Nat, ToolCall.tc_once(ToolCall.tc_ends(es)), List.length(&2, String, ToolCall.tc_journaled(ToolCall.tc_spec(es, False{}))), LA.tp.s_open(es))
