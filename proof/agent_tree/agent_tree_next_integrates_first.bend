# eukhe: the proof of LAW agent_tree_next_integrates_first
#
# PROOF: no message and an arrived result compute to Integrate.

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/patch.bend as LP

def AgentTree.agent_tree_next_integrates_first(n, w):
  {==}
