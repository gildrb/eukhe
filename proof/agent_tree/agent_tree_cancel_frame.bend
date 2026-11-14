# eukhe: the proof of LAW agent_tree_cancel_frame
#
# PROOF: the cancel leaves t or puts a node at p (E.at_edit.edit_at); putting n back where it was gives t (E.at_edit.frame)

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/edit.bend as E


def AgentTree.agent_tree_cancel_frame(b, t, p, n, e):
  %E.at_edit.edit_at(p, t, T.OpCancel{}, T.bound_depth(b)) : {S.put(p, AgentTree.landed(_, t), n) == t : T.Node}
  E.at_edit.frame(T.OpCancel{}, p, t, n, T.bound_depth(b), e)
