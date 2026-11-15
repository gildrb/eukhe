# eukhe: the proof of LAW agent_tree_fail_marks
#
# PROOF: the fail of a running node puts fail_node(n, q) at p
# (E.at_edit.edit_at, E.at_edit.fail_run, E.at_edit.node_at_put); below
# it fail_node cancels each child (cancel_all), whose node at rest has the
# cancel status of the old one (CM.at_cm.gen); a leaf has no node below

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/edit.bend as E
import ./agent_tree_cancel_marks.bend as CM

# the node at d :: rest below fail_node(n, q) has the cancel status of m
def at_fm.below(+d: T.Dir, +rest: List<&2, T.Dir>, +n: T.Node, +q: List<&2, Maybe<&2, Nat>>, -m: T.Node, f: {S.node_at(Con{d, rest}, n) == Some{m} : Maybe<&2, T.Node>}) -> {AgentTree.status_of(S.node_at(Con{d, rest}, T.fail_node(n, q))) == Some{AgentTree.cancel_status(T.st_of(T.info(m)))} : Maybe<&2, T.Status>}:
  match d:
    case T.GoL{}:
      match n:
        case T.Leaf{i}:
          E.at_edit.absurd_none({AgentTree.status_of(None{}) == Some{AgentTree.cancel_status(T.st_of(T.info(m)))} : Maybe<&2, T.Status>}, m, f)
        case T.Split{i, own, l, r}:
          %Equal.sym(Maybe<&2, T.Status>, AgentTree.status_of(S.node_at(rest, T.cancel_all(l))), CM.at_cm.mst(S.node_at(rest, l)), CM.at_cm.gen(rest, l)) : {_ == Some{AgentTree.cancel_status(T.st_of(T.info(m)))} : Maybe<&2, T.Status>}
          %Equal.sym(Maybe<&2, T.Node>, S.node_at(rest, l), Some{m}, f) : {CM.at_cm.mst(_) == Some{AgentTree.cancel_status(T.st_of(T.info(m)))} : Maybe<&2, T.Status>}
          {==}
    case T.GoR{}:
      match n:
        case T.Leaf{i}:
          E.at_edit.absurd_none({AgentTree.status_of(None{}) == Some{AgentTree.cancel_status(T.st_of(T.info(m)))} : Maybe<&2, T.Status>}, m, f)
        case T.Split{i, own, l, r}:
          %Equal.sym(Maybe<&2, T.Status>, AgentTree.status_of(S.node_at(rest, T.cancel_all(r))), CM.at_cm.mst(S.node_at(rest, r)), CM.at_cm.gen(rest, r)) : {_ == Some{AgentTree.cancel_status(T.st_of(T.info(m)))} : Maybe<&2, T.Status>}
          %Equal.sym(Maybe<&2, T.Node>, S.node_at(rest, r), Some{m}, f) : {CM.at_cm.mst(_) == Some{AgentTree.cancel_status(T.st_of(T.info(m)))} : Maybe<&2, T.Status>}
          {==}

def AgentTree.agent_tree_fail_marks(b, t, p, q, n, d, rest, m, e, r, f):
  %E.at_edit.edit_at(p, t, T.OpFail{q}, T.bound_depth(b)) : {AgentTree.status_below(S.node_at(p, AgentTree.landed(_, t)), Con{d, rest}) == Some{AgentTree.cancel_status(T.st_of(T.info(m)))} : Maybe<&2, T.Status>}
  %Equal.sym(Maybe<&2, T.Node>, S.node_at(p, t), Some{n}, e) : {AgentTree.status_below(S.node_at(p, AgentTree.landed(E.at_edit.via(_, p, t, T.OpFail{q}, T.bound_depth(b)), t)), Con{d, rest}) == Some{AgentTree.cancel_status(T.st_of(T.info(m)))} : Maybe<&2, T.Status>}
  %E.at_edit.fail_run(n, q) : {AgentTree.status_below(S.node_at(p, AgentTree.landed(E.at_edit.lift(_, p, t), t)), Con{d, rest}) == Some{AgentTree.cancel_status(T.st_of(T.info(m)))} : Maybe<&2, T.Status>}
  %Equal.sym(Bool, S.is_running(n), True{}, r) : {AgentTree.status_below(S.node_at(p, AgentTree.landed(E.at_edit.lift(E.at_edit.fail_if(_, n, q), p, t), t)), Con{d, rest}) == Some{AgentTree.cancel_status(T.st_of(T.info(m)))} : Maybe<&2, T.Status>}
  %E.at_edit.node_at_put(p, t, n, T.fail_node(n, q), e) : {AgentTree.status_below(_, Con{d, rest}) == Some{AgentTree.cancel_status(T.st_of(T.info(m)))} : Maybe<&2, T.Status>}
  at_fm.below(d, rest, n, q, m, f)
