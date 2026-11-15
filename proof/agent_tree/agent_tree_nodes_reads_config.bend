# eukhe: the proof of LAW agent_tree_nodes_reads_config
#
# PROOF: bound_nodes reads its field of the bounds

import Base
import ../../bend/agent_tree.bend as T
import ../../laws/agent_tree.bend as AgentTree

def AgentTree.agent_tree_nodes_reads_config(d, n, m):
  {==}
