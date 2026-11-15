# eukhe: the proof of LAW agent_tree_cancel_takes
#
# PROOF: the cancel is the edit at p (E.at_edit.edit_at), which with the
# node n at p is the local cancel of n, always Took{cancel_all(n)}, put
# back at p

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/edit.bend as E

def AgentTree.agent_tree_cancel_takes(b, t, p, n, e):
  %E.at_edit.edit_at(p, t, T.OpCancel{}, T.bound_depth(b)) : {AgentTree.took(_) == True{} : Bool}
  %Equal.sym(Maybe<&2, T.Node>, S.node_at(p, t), Some{n}, e) : {AgentTree.took(E.at_edit.via(_, p, t, T.OpCancel{}, T.bound_depth(b))) == True{} : Bool}
  {==}
