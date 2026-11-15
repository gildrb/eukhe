# eukhe: the proof of LAW agent_tree_init_blank
#
# PROOF: the root's integrated patch is its own patch, which is empty;
# case on f: the empty patch keeps both the empty files and any others

import Base
import ../../bend/agent_tree.bend as T
import ../../laws/agent_tree.bend as AgentTree

def AgentTree.agent_tree_init_blank(s, lim, dl, f):
  match f:
    case Nil{}:
      {==}
    case Con{x, xt}:
      {==}
