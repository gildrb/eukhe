# eukhe: the proof of LAW agent_tree_overlay_applies
#
# PROOF: induction on the files following T.overlay's cases (LP.at_patch.overlay_applies): apply on [] is [], an empty patch changes nothing, a child write inside the scope lands over the parent's.

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/patch.bend as LP

def AgentTree.agent_tree_overlay_applies(f, c, a, s):
  LP.at_patch.overlay_applies(f, c, a, s)
