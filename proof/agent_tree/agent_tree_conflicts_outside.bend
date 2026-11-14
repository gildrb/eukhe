# eukhe: the proof of LAW agent_tree_conflicts_outside
#
# PROOF: induction on the child patch and the scope (LP.at_patch.outside): a conflict is a write and not a scope unit.

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/patch.bend as LP

def AgentTree.agent_tree_conflicts_outside(a, s):
  LP.at_patch.outside(a, s)
