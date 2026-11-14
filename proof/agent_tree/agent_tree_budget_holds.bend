# eukhe: the proof of LAW agent_tree_budget_holds
#
# PROOF: Good (kept by every event) says each split's own spend plus what its children hold fits its limit and each leaf's spend fits its limit; a child holds at least what its subtree spent, so the whole tree's spend fits the root's limit, which no event changes. The invariant and its preservation are in base/reach.bend.

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/reach.bend as AR

def AgentTree.agent_tree_budget_holds(evs, b, s, lim, dl):
  AR.at_reach.budget_holds(evs, b, s, lim, dl)
