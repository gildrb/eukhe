# eukhe: the proof of LAW agent_tree_conflicts_cover
#
# PROOF: induction on the child patch and the scope (LP.at_patch.cover): unit by unit a write is inside the scope (restricted) or outside it (a conflict).

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/patch.bend as LP

def AgentTree.agent_tree_conflicts_cover(a, s):
  LP.at_patch.cover(a, s)
