# eukhe: the proof of LAW crown_init_steps_as_tree
#
# PROOF: cinit(s, lim, dl) is the crown of init(s, lim, dl) with no help
# leaf, so crown_tree_alone at that tree

import Base
import ../../bend/agent_tree.bend as T
import ../../bend/agent_crown.bend as A
import ../../laws/agent_crown.bend as AgentCrown
import ./crown_tree_alone.bend as Alone

def AgentCrown.crown_init_steps_as_tree(b, s, lim, dl, e):
  AgentCrown.crown_tree_alone(b, T.init(s, lim, dl), e)
