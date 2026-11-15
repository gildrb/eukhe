# eukhe: the proof of LAW agent_tree_fail_shape
#
# PROOF: the fail of a running node puts fail_node(n, q) at p
# (E.at_edit.edit_at, E.at_edit.fail_run, E.at_edit.node_at_put);
# fail_node settles n's info with q and cancels its children, which with
# the statuses forgotten is n with its patch q (at_fs.node; the children by
# CS.at_cs.gen)

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/edit.bend as E
import ./agent_tree_cancel_shape.bend as CS

# a settled info, its status forgotten, is the info with the new patch
def at_fs.info(+i: T.Info, +st: T.Status, +q: List<&2, Maybe<&2, Nat>>) -> {AgentTree.unstatus_info(T.settle_info(i, st, q)) == AgentTree.unstatus_info(AgentTree.patch_info(i, q)) : T.Info}:
  match i:
    case T.Info{old, s, lim, sp, dl, p}:
      {==}

# fail_node(n, q) with the statuses forgotten is n with its patch q
def at_fs.node(+n: T.Node, +q: List<&2, Maybe<&2, Nat>>) -> {AgentTree.unstatus(T.fail_node(n, q)) == AgentTree.unstatus(AgentTree.with_patch(n, q)) : T.Node}:
  match n:
    case T.Leaf{i}:
      %Equal.sym(T.Info, AgentTree.unstatus_info(T.settle_info(i, T.Failed{}, q)), AgentTree.unstatus_info(AgentTree.patch_info(i, q)), at_fs.info(i, T.Failed{}, q)) : {T.Leaf{_} == T.Leaf{AgentTree.unstatus_info(AgentTree.patch_info(i, q))} : T.Node}
      {==}
    case T.Split{i, own, l, r}:
      %Equal.sym(T.Node, AgentTree.unstatus(T.cancel_all(l)), AgentTree.unstatus(l), CS.at_cs.gen(l)) : {T.Split{AgentTree.unstatus_info(T.settle_info(i, T.Failed{}, q)), own, _, AgentTree.unstatus(T.cancel_all(r))} == T.Split{AgentTree.unstatus_info(AgentTree.patch_info(i, q)), own, AgentTree.unstatus(l), AgentTree.unstatus(r)} : T.Node}
      %Equal.sym(T.Node, AgentTree.unstatus(T.cancel_all(r)), AgentTree.unstatus(r), CS.at_cs.gen(r)) : {T.Split{AgentTree.unstatus_info(T.settle_info(i, T.Failed{}, q)), own, AgentTree.unstatus(l), _} == T.Split{AgentTree.unstatus_info(AgentTree.patch_info(i, q)), own, AgentTree.unstatus(l), AgentTree.unstatus(r)} : T.Node}
      %Equal.sym(T.Info, AgentTree.unstatus_info(T.settle_info(i, T.Failed{}, q)), AgentTree.unstatus_info(AgentTree.patch_info(i, q)), at_fs.info(i, T.Failed{}, q)) : {T.Split{_, own, AgentTree.unstatus(l), AgentTree.unstatus(r)} == T.Split{AgentTree.unstatus_info(AgentTree.patch_info(i, q)), own, AgentTree.unstatus(l), AgentTree.unstatus(r)} : T.Node}
      {==}

def AgentTree.agent_tree_fail_shape(b, t, p, q, n, e, r):
  %E.at_edit.edit_at(p, t, T.OpFail{q}, T.bound_depth(b)) : {AgentTree.unstatus_of(S.node_at(p, AgentTree.landed(_, t))) == Some{AgentTree.unstatus(AgentTree.with_patch(n, q))} : Maybe<&2, T.Node>}
  %Equal.sym(Maybe<&2, T.Node>, S.node_at(p, t), Some{n}, e) : {AgentTree.unstatus_of(S.node_at(p, AgentTree.landed(E.at_edit.via(_, p, t, T.OpFail{q}, T.bound_depth(b)), t))) == Some{AgentTree.unstatus(AgentTree.with_patch(n, q))} : Maybe<&2, T.Node>}
  %E.at_edit.fail_run(n, q) : {AgentTree.unstatus_of(S.node_at(p, AgentTree.landed(E.at_edit.lift(_, p, t), t))) == Some{AgentTree.unstatus(AgentTree.with_patch(n, q))} : Maybe<&2, T.Node>}
  %Equal.sym(Bool, S.is_running(n), True{}, r) : {AgentTree.unstatus_of(S.node_at(p, AgentTree.landed(E.at_edit.lift(E.at_edit.fail_if(_, n, q), p, t), t))) == Some{AgentTree.unstatus(AgentTree.with_patch(n, q))} : Maybe<&2, T.Node>}
  %E.at_edit.node_at_put(p, t, n, T.fail_node(n, q), e) : {AgentTree.unstatus_of(_) == Some{AgentTree.unstatus(AgentTree.with_patch(n, q))} : Maybe<&2, T.Node>}
  %Equal.sym(T.Node, AgentTree.unstatus(T.fail_node(n, q)), AgentTree.unstatus(AgentTree.with_patch(n, q)), at_fs.node(n, q)) : {Some{_} == Some{AgentTree.unstatus(AgentTree.with_patch(n, q))} : Maybe<&2, T.Node>}
  {==}
