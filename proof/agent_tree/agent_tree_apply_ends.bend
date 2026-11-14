# eukhe: the proof of LAW agent_tree_apply_ends
#
# PROOF: by cases on the files: apply's arms with an empty patch return them

import Base
import ../../bend/agent_tree.bend as T
import ../../laws/agent_tree.bend as AgentTree

def AgentTree.agent_tree_apply_ends(f):
  match f:
    case []:
      {==}
    case x <> xt:
      {==}
