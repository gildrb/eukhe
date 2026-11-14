# eukhe: the proof of LAW agent_tree_finish_is_spec
#
# PROOF: the step is the edit at p through the spec's node (E.at_edit.edit_at); by the node's shape and status the code's finish is the spec's (E.at_edit.finish_m)

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/edit.bend as E


def AgentTree.agent_tree_finish_is_spec(b, t, p, q):
  %E.at_edit.edit_at(p, t, T.OpFinish{q}, T.bound_depth(b)) : {_ == AgentTree.finish_spec(t, p, q) : T.Step}
  E.at_edit.finish_m(S.node_at(p, t), t, p, q, T.bound_depth(b))
