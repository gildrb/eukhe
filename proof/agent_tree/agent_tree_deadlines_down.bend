# eukhe: the proof of LAW agent_tree_deadlines_down
#
# PROOF: Good (kept by every event) says each child's deadline is at most its parent's. The invariant and its preservation are in base/reach.bend.

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/reach.bend as AR

def AgentTree.agent_tree_deadlines_down(evs, b, s, lim, dl):
  AR.at_reach.deadlines_down(evs, b, s, lim, dl)
