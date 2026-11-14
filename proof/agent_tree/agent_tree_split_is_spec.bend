# eukhe: the proof of LAW agent_tree_split_is_spec
#
# PROOF: the step is the edit at p, which is the spec's node at p handed to local and put back (E.at_edit.edit_at); for each node the code's checks are the spec's (E.at_edit.split_m: depth gate, size = nodes, tiles = splits, any = owns_some, free = room) and the new split is split_node

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/edit.bend as E


def AgentTree.agent_tree_split_is_spec(b, t, p, own, ls, rs, hold):
  %E.at_edit.edit_at(p, t, E.at_edit.split_op(b, t, own, ls, rs, hold), T.bound_depth(b)) : {_ == AgentTree.split_spec(b, t, p, own, ls, rs, hold) : T.Step}
  E.at_edit.split_m(S.node_at(p, t), b, t, p, own, ls, rs, hold)
