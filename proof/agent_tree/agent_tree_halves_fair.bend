# eukhe: the proof of LAW agent_tree_halves_fair
#
# PROOF: half(c) is Nat.div(c, 2n), the two-step h(c) (LP.at_patch.div2, by Nat.divmod.go); c - h(c) is hi(c) with h(c) + hi(c) == c, and hi(c) is h(c) or one more, by two-step induction (LP.at_patch.fair).

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/patch.bend as LP

def AgentTree.agent_tree_halves_fair(c):
  LP.at_patch.fair(c)
