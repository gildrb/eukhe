# eukhe: the proof of LAW agent_tree_fail_needs_node
#
# PROOF: the fail is the edit at p (E.at_edit.edit_at), which with no
# node at p is refused NoNode

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/edit.bend as E

def AgentTree.agent_tree_fail_needs_node(b, t, p, q, e):
  %E.at_edit.edit_at(p, t, T.OpFail{q}, T.bound_depth(b)) : {_ == T.Refused{T.NoNode{}} : T.Step}
  %Equal.sym(Maybe<&2, T.Node>, S.node_at(p, t), None{}, e) : {E.at_edit.via(_, p, t, T.OpFail{q}, T.bound_depth(b)) == T.Refused{T.NoNode{}} : T.Step}
  {==}
