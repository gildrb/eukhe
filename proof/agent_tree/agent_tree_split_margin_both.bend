# eukhe: the proof of LAW agent_tree_split_margin_both
#
# PROOF: by computation once k is split (the node check 3 <= 3 + k
# reduces on k's first constructor)

import Base
import ../../bend/agent_tree.bend as T
import ../../laws/agent_tree.bend as AgentTree

def AgentTree.agent_tree_split_margin_both(d, k, m, x):
  match k:
    case 0n:
      {==}
    case 1n+j:
      {==}
