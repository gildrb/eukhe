# eukhe: the proof of LAW agent_tree_cancel_keeps
#
# PROOF: the cancel puts cancel_all(n) at p (E.at_edit.edit_at,
# E.at_edit.node_at_put); below it, the node at q of cancel_all(n) has the
# cancel info of the node at q of n (at_ck.gen, induction on q), which is m

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/edit.bend as E

# the cancel info of the node mm (none: None)
def at_ck.mst(mm: Maybe<&2, T.Node>) -> Maybe<&2, T.Info>:
  match mm:
    case None{}:
      None{}
    case Some{x}:
      Some{AgentTree.cancel_info_spec(T.info(x))}

# the code's cancel of one info is the spec's, inside Some
def at_ck.info(+i: T.Info) -> {Some{T.cancel_info(i)} == Some{AgentTree.cancel_info_spec(i)} : Maybe<&2, T.Info>}:
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

# the node at q of cancel_all(n) has the cancel info of the node at q of n
def at_ck.gen(+q: List<&2, T.Dir>, +n: T.Node) -> {AgentTree.info_of(S.node_at(q, T.cancel_all(n))) == at_ck.mst(S.node_at(q, n)) : Maybe<&2, T.Info>}:
  match q:
    case Nil{}:
      match n:
        case T.Leaf{i}:
          at_ck.info(i)
        case T.Split{i, own, l, r}:
          at_ck.info(i)
    case Con{d, rest}:
      match d:
        case T.GoL{}:
          match n:
            case T.Leaf{i}:
              {==}
            case T.Split{i, own, l, r}:
              at_ck.gen(rest, l)
        case T.GoR{}:
          match n:
            case T.Leaf{i}:
              {==}
            case T.Split{i, own, l, r}:
              at_ck.gen(rest, r)

def AgentTree.agent_tree_cancel_keeps(b, t, p, n, q, m, e, f):
  %E.at_edit.edit_at(p, t, T.OpCancel{}, T.bound_depth(b)) : {AgentTree.info_below(S.node_at(p, AgentTree.landed(_, t)), q) == Some{AgentTree.cancel_info_spec(T.info(m))} : Maybe<&2, T.Info>}
  %Equal.sym(Maybe<&2, T.Node>, S.node_at(p, t), Some{n}, e) : {AgentTree.info_below(S.node_at(p, AgentTree.landed(E.at_edit.via(_, p, t, T.OpCancel{}, T.bound_depth(b)), t)), q) == Some{AgentTree.cancel_info_spec(T.info(m))} : Maybe<&2, T.Info>}
  %E.at_edit.node_at_put(p, t, n, T.cancel_all(n), e) : {AgentTree.info_below(_, q) == Some{AgentTree.cancel_info_spec(T.info(m))} : Maybe<&2, T.Info>}
  %Equal.sym(Maybe<&2, T.Info>, AgentTree.info_of(S.node_at(q, T.cancel_all(n))), at_ck.mst(S.node_at(q, n)), at_ck.gen(q, n)) : {_ == Some{AgentTree.cancel_info_spec(T.info(m))} : Maybe<&2, T.Info>}
  %Equal.sym(Maybe<&2, T.Node>, S.node_at(q, n), Some{m}, f) : {at_ck.mst(_) == Some{AgentTree.cancel_info_spec(T.info(m))} : Maybe<&2, T.Info>}
  {==}
