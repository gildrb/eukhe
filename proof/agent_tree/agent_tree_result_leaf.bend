# eukhe: the proof of LAW agent_tree_result_leaf
#
# PROOF: a leaf's result is its patch (T.result), so both sides are one
# apply

import Base
import ../../bend/agent_tree.bend as T
import ../../laws/agent_tree.bend as AgentTree

def AgentTree.agent_tree_result_leaf(i, f):
  {==}
