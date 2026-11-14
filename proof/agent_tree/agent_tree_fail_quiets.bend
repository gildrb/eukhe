# eukhe: the proof of LAW agent_tree_fail_quiets
#
# PROOF: the fail of a running node puts fail_node at p (E.at_edit.edit_at, E.at_edit.fail_run), the node at p is then that one (E.at_edit.node_at_put): failed with q, its children cancelled (E.at_edit.failed_node)

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/edit.bend as E


def AgentTree.agent_tree_fail_quiets(b, t, p, q, n, e, r):
  %E.at_edit.edit_at(p, t, T.OpFail{q}, T.bound_depth(b)) : {AgentTree.failed_with(S.node_at(p, AgentTree.landed(_, t)), q) == True{} : Bool}
  E.at_edit.fail_q(p, t, q, n, T.bound_depth(b), e, r)
