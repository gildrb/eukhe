# eukhe: the proof of LAW agent_tree_cancel_quiets
#
# PROOF: the cancel puts cancel_all(n) at p (E.at_edit.edit_at), the node at p is then that one (E.at_edit.node_at_put), and cancel_all quiets a subtree (E.at_edit.quiet_cancel)

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/edit.bend as E


def AgentTree.agent_tree_cancel_quiets(b, t, p, n, e):
  %E.at_edit.edit_at(p, t, T.OpCancel{}, T.bound_depth(b)) : {AgentTree.quiet_at(p, AgentTree.landed(_, t)) == True{} : Bool}
  E.at_edit.cancel_q(p, t, n, T.bound_depth(b), e)
