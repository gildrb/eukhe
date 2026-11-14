# eukhe: the proof of LAW agent_tree_tick_none_late
#
# PROOF: induction on the tree with the cut flag generalized (E.at_edit.tick_late): each ticked node is cancelled or not late (E.at_edit.head)

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/edit.bend as E


def AgentTree.agent_tree_tick_none_late(b, t, now):
  E.at_edit.tick_late(t, now, False{})
