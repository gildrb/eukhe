# eukhe: the proof of LAW agent_tree_next_message_first
#
# PROOF: a message computes to ReadMessage.

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/patch.bend as LP

def AgentTree.agent_tree_next_message_first(n, w):
  {==}
