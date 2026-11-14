# eukhe: the proof of LAW agent_tree_done_settled
#
# PROOF: Good (kept by every event) says a split that does not run, a finished one included, has children that do not run. The invariant and its preservation are in base/reach.bend.

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/reach.bend as AR

def AgentTree.agent_tree_done_settled(evs, b, s, lim, dl):
  AR.at_reach.done_settled(evs, b, s, lim, dl)
