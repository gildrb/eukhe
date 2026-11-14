# eukhe: the proof of LAW agent_tree_apply_lands
#
# PROOF: by computation: apply's cons arm lands each write on its unit

import Base
import ../../bend/agent_tree.bend as T
import ../../laws/agent_tree.bend as AgentTree

def AgentTree.agent_tree_apply_lands(x, y, z, f, p):
  {==}
