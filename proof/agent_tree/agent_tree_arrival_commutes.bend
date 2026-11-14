# eukhe: the proof of LAW agent_tree_arrival_commutes
#
# PROOF: both sides are the files with c then the two restricted child patches (LP.at_patch.overlay_applies_r twice); restrictions to disjoint scopes write disjoint units (LP.at_patch.dw_restrict) and so commute (LP.at_patch.commute).

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/patch.bend as LP

def AgentTree.agent_tree_arrival_commutes(f, c, a, sa, x, sb, e):
  LP.at_patch.arrival(f, c, a, sa, x, sb, e)
