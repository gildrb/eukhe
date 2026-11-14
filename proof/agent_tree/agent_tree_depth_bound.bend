# eukhe: the proof of LAW agent_tree_depth_bound
#
# PROOF: Good(t, max_depth) (kept by every event) spends one level of the depth budget per split, so depth(t) <= max_depth. The invariant and its preservation are in base/reach.bend.

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/reach.bend as AR

def AgentTree.agent_tree_depth_bound(evs, b, s, lim, dl):
  AR.at_reach.depth_bound(evs, b, s, lim, dl)
