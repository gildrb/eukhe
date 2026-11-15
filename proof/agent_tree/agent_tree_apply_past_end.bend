# eukhe: the proof of LAW agent_tree_apply_past_end
#
# PROOF: by cases on the patch: apply's arms with no files return none

import Base
import ../../bend/agent_tree.bend as T
import ../../laws/agent_tree.bend as AgentTree

def AgentTree.agent_tree_apply_past_end(p):
  match p:
    case []:
      {==}
    case y <> yt:
      {==}
