# eukhe: the proof of LAW stream_settle_carries_all
# The replies are S2's (LA.tp.model): every report before the end is
# stored (LA.tp.k_open), none after it (LA.tp.k_over).

import Base
import ../../laws/tool_call.bend as ToolCall
import ./base.bend as LA

def ToolCall.stream_settle_carries_all(first, es):
  %LA.tp.model(first, es) : {ToolCall.tc_kept(es, _) == ToolCall.tc_before_end(es, False{}) : List<&2, Bool>}
  LA.tp.k_open(es)
