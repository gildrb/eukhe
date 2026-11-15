# eukhe: the proof of LAW agent_tree_tick_marks
#
# PROOF: a tick is taken with tick(t, now, False); each node's info is kept
# or cancelled (at_tm.info), and the node at q of tick(t, now, cut) is the
# tick of the node at q of t under some cut (at_tm.gen, induction on q
# generalizing cut); the premise puts m at q

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree

# the moves allowed from the node mn (none: True)
def at_tm.ok(mn: Maybe<&2, T.Node>, s: Maybe<&2, T.Status>) -> Bool:
  match mn:
    case None{}:
      True{}
    case Some{x}:
      AgentTree.tick_moves(s, T.st_of(T.info(x)))

# a tick's info keeps the status or cancels it
def at_tm.info(+up: Bool, +i: T.Info) -> {AgentTree.tick_moves(Some{T.st_of(T.tick_info(up, i))}, T.st_of(i)) == True{} : Bool}:
  match up:
    case False{}:
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
    case True{}:
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

# the node at q of tick(t, now, cut) moved as allowed from the node at q of t
def at_tm.gen(+q: List<&2, T.Dir>, +t: T.Node, +now: Nat, +cut: Bool) -> {at_tm.ok(S.node_at(q, t), AgentTree.status_of(S.node_at(q, T.tick(t, now, cut)))) == True{} : Bool}:
  match q:
    case Nil{}:
      match t:
        case T.Leaf{i}:
          at_tm.info(Bool.or(cut, T.expired(i, now)), i)
        case T.Split{i, own, l, r}:
          at_tm.info(Bool.or(cut, T.expired(i, now)), i)
    case Con{d, rest}:
      match d:
        case T.GoL{}:
          match t:
            case T.Leaf{i}:
              {==}
            case T.Split{i, own, l, r}:
              at_tm.gen(rest, l, now, Bool.or(cut, T.expired(i, now)))
        case T.GoR{}:
          match t:
            case T.Leaf{i}:
              {==}
            case T.Split{i, own, l, r}:
              at_tm.gen(rest, r, now, Bool.or(cut, T.expired(i, now)))

def AgentTree.agent_tree_tick_marks(b, t, now, q, m, e):
  %e : {at_tm.ok(_, AgentTree.status_of(S.node_at(q, T.tick(t, now, False{})))) == True{} : Bool}
  at_tm.gen(q, t, now, False{})
