# eukhe: the proof of LAW agent_tree_depth_configured
#
# PROOF: agent_tree_depth_bound at the bounds Bounds{d, n, m}, whose
# bound_depth is d

import Base
import ../../bend/agent_tree.bend as T
import ../../laws/agent_tree.bend as AgentTree

def AgentTree.agent_tree_depth_configured(evs, d, n, m, s, lim, dl):
  AgentTree.agent_tree_depth_bound(evs, T.Bounds{d, n, m}, s, lim, dl)
