# eukhe: the proof of LAW agent_tree_no_orphan
#
# PROOF: Good (kept by every event) says a split that does not run has children that do not run; by induction everything below such a node is quiet. The invariant and its preservation are in base/reach.bend.

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/reach.bend as AR

def AgentTree.agent_tree_no_orphan(evs, b, s, lim, dl):
  AR.at_reach.no_orphan(evs, b, s, lim, dl)
