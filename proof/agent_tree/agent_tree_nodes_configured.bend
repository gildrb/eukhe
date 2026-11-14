# eukhe: the proof of LAW agent_tree_nodes_configured
#
# PROOF: agent_tree_nodes_bound at the bounds Bounds{d, 1+n, m}, whose
# bound_nodes is 1+n (at least one)

import Base
import ../../bend/agent_tree.bend as T
import ../../laws/agent_tree.bend as AgentTree

def AgentTree.agent_tree_nodes_configured(evs, d, n, m, s, lim, dl):
  match n:
    case 0n:
      AgentTree.agent_tree_nodes_bound(evs, T.Bounds{d, 1n, m}, s, lim, dl, {==})
    case 1n+j:
      AgentTree.agent_tree_nodes_bound(evs, T.Bounds{d, 2n+j, m}, s, lim, dl, {==})
