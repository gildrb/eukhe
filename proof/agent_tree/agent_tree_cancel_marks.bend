# eukhe: the proof of LAW agent_tree_cancel_marks
#
# PROOF: the cancel puts cancel_all(n) at p (E.at_edit.edit_at,
# E.at_edit.node_at_put); below it, the node at q of cancel_all(n) has the
# cancel status of the node at q of n (at_cm.gen, induction on q), which is m

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/edit.bend as E

# the cancel status of the node mm (none: None)
def at_cm.mst(mm: Maybe<&2, T.Node>) -> Maybe<&2, T.Status>:
  match mm:
    case None{}:
      None{}
    case Some{x}:
      Some{AgentTree.cancel_status(T.st_of(T.info(x)))}

# the code's cancel status of one info is the spec's, inside Some
def at_cm.info(+i: T.Info) -> {Some{T.st_of(T.cancel_info(i))} == Some{AgentTree.cancel_status(T.st_of(i))} : Maybe<&2, T.Status>}:
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

# the node at q of cancel_all(n) has the cancel status of the node at q of n
def at_cm.gen(+q: List<&2, T.Dir>, +n: T.Node) -> {AgentTree.status_of(S.node_at(q, T.cancel_all(n))) == at_cm.mst(S.node_at(q, n)) : Maybe<&2, T.Status>}:
  match q:
    case Nil{}:
      match n:
        case T.Leaf{i}:
          at_cm.info(i)
        case T.Split{i, own, l, r}:
          at_cm.info(i)
    case Con{d, rest}:
      match d:
        case T.GoL{}:
          match n:
            case T.Leaf{i}:
              {==}
            case T.Split{i, own, l, r}:
              at_cm.gen(rest, l)
        case T.GoR{}:
          match n:
            case T.Leaf{i}:
              {==}
            case T.Split{i, own, l, r}:
              at_cm.gen(rest, r)

def AgentTree.agent_tree_cancel_marks(b, t, p, n, q, m, e, f):
  %E.at_edit.edit_at(p, t, T.OpCancel{}, T.bound_depth(b)) : {AgentTree.status_below(S.node_at(p, AgentTree.landed(_, t)), q) == Some{AgentTree.cancel_status(T.st_of(T.info(m)))} : Maybe<&2, T.Status>}
  %Equal.sym(Maybe<&2, T.Node>, S.node_at(p, t), Some{n}, e) : {AgentTree.status_below(S.node_at(p, AgentTree.landed(E.at_edit.via(_, p, t, T.OpCancel{}, T.bound_depth(b)), t)), q) == Some{AgentTree.cancel_status(T.st_of(T.info(m)))} : Maybe<&2, T.Status>}
  %E.at_edit.node_at_put(p, t, n, T.cancel_all(n), e) : {AgentTree.status_below(_, q) == Some{AgentTree.cancel_status(T.st_of(T.info(m)))} : Maybe<&2, T.Status>}
  %Equal.sym(Maybe<&2, T.Status>, AgentTree.status_of(S.node_at(q, T.cancel_all(n))), at_cm.mst(S.node_at(q, n)), at_cm.gen(q, n)) : {_ == Some{AgentTree.cancel_status(T.st_of(T.info(m)))} : Maybe<&2, T.Status>}
  %Equal.sym(Maybe<&2, T.Node>, S.node_at(q, n), Some{m}, f) : {at_cm.mst(_) == Some{AgentTree.cancel_status(T.st_of(T.info(m)))} : Maybe<&2, T.Status>}
  {==}
