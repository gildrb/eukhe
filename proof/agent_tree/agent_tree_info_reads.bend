# eukhe: the proof of LAW agent_tree_info_reads
#
# PROOF: by cases on the Info: every reader returns its field

import Base
import ../../bend/agent_tree.bend as T
import ../../laws/agent_tree.bend as AgentTree

def AgentTree.agent_tree_info_reads(i, own, l, r):
  match i:
    case T.Info{st, s, lim, sp, dl, p}:
      {==}
