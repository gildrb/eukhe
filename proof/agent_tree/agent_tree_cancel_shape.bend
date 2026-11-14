# eukhe: the proof of LAW agent_tree_cancel_shape
#
# PROOF: the cancel puts cancel_all(n) at p (E.at_edit.edit_at,
# E.at_edit.node_at_put); cancel_all changes statuses only, so with the
# statuses forgotten it is n (at_cs.gen, induction on n)

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/edit.bend as E

# the code's cancel of one info, its status forgotten, is the info's
def at_cs.info(+i: T.Info) -> {AgentTree.unstatus_info(T.cancel_info(i)) == AgentTree.unstatus_info(i) : T.Info}:
  match i:
    case T.Info{st, s, lim, sp, dl, p}:
      match st:
        case T.Running{}:
          {==}
        case T.Finished{}:
          {==}
        case T.Failed{}:
          {==}
        case T.Cancelled{}:
          {==}

# cancel_all(n) with the statuses forgotten is n with the statuses forgotten
def at_cs.gen(+n: T.Node) -> {AgentTree.unstatus(T.cancel_all(n)) == AgentTree.unstatus(n) : T.Node}:
  match n:
    case T.Leaf{i}:
      %Equal.sym(T.Info, AgentTree.unstatus_info(T.cancel_info(i)), AgentTree.unstatus_info(i), at_cs.info(i)) : {T.Leaf{_} == T.Leaf{AgentTree.unstatus_info(i)} : T.Node}
      {==}
    case T.Split{i, own, l, r}:
      %Equal.sym(T.Node, AgentTree.unstatus(T.cancel_all(l)), AgentTree.unstatus(l), at_cs.gen(l)) : {T.Split{AgentTree.unstatus_info(T.cancel_info(i)), own, _, AgentTree.unstatus(T.cancel_all(r))} == T.Split{AgentTree.unstatus_info(i), own, AgentTree.unstatus(l), AgentTree.unstatus(r)} : T.Node}
      %Equal.sym(T.Node, AgentTree.unstatus(T.cancel_all(r)), AgentTree.unstatus(r), at_cs.gen(r)) : {T.Split{AgentTree.unstatus_info(T.cancel_info(i)), own, AgentTree.unstatus(l), _} == T.Split{AgentTree.unstatus_info(i), own, AgentTree.unstatus(l), AgentTree.unstatus(r)} : T.Node}
      %Equal.sym(T.Info, AgentTree.unstatus_info(T.cancel_info(i)), AgentTree.unstatus_info(i), at_cs.info(i)) : {T.Split{_, own, AgentTree.unstatus(l), AgentTree.unstatus(r)} == T.Split{AgentTree.unstatus_info(i), own, AgentTree.unstatus(l), AgentTree.unstatus(r)} : T.Node}
      {==}

def AgentTree.agent_tree_cancel_shape(b, t, p, n, e):
  %E.at_edit.edit_at(p, t, T.OpCancel{}, T.bound_depth(b)) : {AgentTree.unstatus_of(S.node_at(p, AgentTree.landed(_, t))) == Some{AgentTree.unstatus(n)} : Maybe<&2, T.Node>}
  %Equal.sym(Maybe<&2, T.Node>, S.node_at(p, t), Some{n}, e) : {AgentTree.unstatus_of(S.node_at(p, AgentTree.landed(E.at_edit.via(_, p, t, T.OpCancel{}, T.bound_depth(b)), t))) == Some{AgentTree.unstatus(n)} : Maybe<&2, T.Node>}
  %E.at_edit.node_at_put(p, t, n, T.cancel_all(n), e) : {AgentTree.unstatus_of(_) == Some{AgentTree.unstatus(n)} : Maybe<&2, T.Node>}
  %Equal.sym(T.Node, AgentTree.unstatus(T.cancel_all(n)), AgentTree.unstatus(n), at_cs.gen(n)) : {Some{_} == Some{AgentTree.unstatus(n)} : Maybe<&2, T.Node>}
  {==}
