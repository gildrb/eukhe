# eukhe: the proof of LAW agent_tree_tick_cancels_late_below
#
# PROOF: the tick step is Took{T.tick(t, now, False)}; induction on p under the cut flag c (LT.at_tick.late_below): with c True no node at any path runs (at_tick.cut_stops: cancel_info's status never runs); with c False the head is late or not (at_tick.late_eq turns late into expired, the flag below): a late end is cancelled (at_tick.cut_base), a split's flag below is its own lateness, and the path from there on is not on time unless the flag is set.

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/tick.bend as LT

def AgentTree.agent_tree_tick_cancels_late_below(b, t, p, now, n, e, o):
  LT.at_tick.late_below(p, False{}, t, now, o)
