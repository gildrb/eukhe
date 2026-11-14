# eukhe: the proof of LAW agent_tree_nodes_bound
#
# PROOF: init has one node; a split is admitted only when size + 2 <= max_nodes and adds exactly two nodes, every other event keeps the size; nodes = size. The invariant and its preservation are in base/reach.bend.

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/reach.bend as AR

def AgentTree.agent_tree_nodes_bound(evs, b, s, lim, dl, e):
  AR.at_reach.nodes_bound(evs, b, s, lim, dl, e)
