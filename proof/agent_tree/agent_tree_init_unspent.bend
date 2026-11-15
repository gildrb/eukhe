# eukhe: the proof of LAW agent_tree_init_unspent
#
# PROOF: the root is a leaf with nothing spent; its subtree spend is its own

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree

def AgentTree.agent_tree_init_unspent(s, lim, dl):
  {==}
