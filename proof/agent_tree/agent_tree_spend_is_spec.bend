# eukhe: the proof of LAW agent_tree_spend_is_spec
#
# PROOF: the step is the edit at p through the spec's node (E.at_edit.edit_at); a running node's free is its room (E.at_edit.fits), so the code's spend is the spec's (E.at_edit.spend_m)

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/edit.bend as E


def AgentTree.agent_tree_spend_is_spec(b, t, p, a):
  %E.at_edit.edit_at(p, t, T.OpSpend{a}, T.bound_depth(b)) : {_ == AgentTree.spend_spec(t, p, a) : T.Step}
  E.at_edit.spend_m(S.node_at(p, t), t, p, a, T.bound_depth(b))
