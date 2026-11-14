# eukhe: the proof of LAW agent_tree_tiles_root
#
# PROOF: the root's scope is tiled by every reachable tree: Good keeps each split's tile equal to its scope's counts, so by induction tile(t) = counts(scope(root)), and no event changes the root's scope. The invariant and its preservation are in base/reach.bend.

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/reach.bend as AR

def AgentTree.agent_tree_tiles_root(evs, b, s, lim, dl):
  AR.at_reach.tiles_root(evs, b, s, lim, dl)
