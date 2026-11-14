# eukhe: the proof of LAW agent_tree_tick_cancels_only_late
#
# PROOF: the tick step is Took{T.tick(t, now, False)}; induction on p (LT.at_tick.keeps): on an on-time path each node is not expired (at_tick.exp_false), so the cut flag stays False down to n, which runs and is not late, so its tick keeps it Running (at_tick.tinfo).

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/tick.bend as LT

def AgentTree.agent_tree_tick_cancels_only_late(b, t, p, now, n, e, r, o):
  LT.at_tick.keeps(p, t, now, n, e, r, o)
