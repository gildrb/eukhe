# eukhe: the proof of LAW agent_tree_fail_frame
#
# PROOF: the fail leaves t or puts a node at p (E.at_edit.edit_at); putting n back where it was gives t (E.at_edit.frame)

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/edit.bend as E


def AgentTree.agent_tree_fail_frame(b, t, p, q, n, e):
  %E.at_edit.edit_at(p, t, T.OpFail{q}, T.bound_depth(b)) : {S.put(p, AgentTree.landed(_, t), n) == t : T.Node}
  E.at_edit.frame(T.OpFail{q}, p, t, n, T.bound_depth(b), e)
