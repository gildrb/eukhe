# eukhe: the proof of LAW stream_journals_two
# The journal is the open's record and the settles the replies ask; the
# replies are S2's (LA.tp.model), which ask one settle at most
# (LA.tp.s_open): 1 + 1 at most is at most 2.

import Base
import ../../laws/tool_call.bend as ToolCall
import ./base.bend as LA

def ToolCall.stream_journals_two(first, es):
  %LA.tp.model(first, es) : {Nat.is_le(1n+List.length(&2, String, ToolCall.tc_journaled(_)), 2n) == True{} : Bool}
  %LA.tp.s_open(es) : {Nat.is_le(1n+_, 2n) == True{} : Bool}
  LA.tp.le_once(ToolCall.tc_ends(es))
