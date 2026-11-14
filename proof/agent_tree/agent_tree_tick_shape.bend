# eukhe: the proof of LAW agent_tree_tick_shape
#
# PROOF: a tick is taken with tick(t, now, False); each node's info is
# kept or cancelled (at_ts.info: the same with the status forgotten), so
# induction on the tree generalizing cut (at_ts.gen)

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree

# a tick's info, its status forgotten, is the info's
def at_ts.info(+up: Bool, +i: T.Info) -> {AgentTree.unstatus_info(T.tick_info(up, i)) == AgentTree.unstatus_info(i) : T.Info}:
  match up:
    case False{}:
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

# tick(t, now, cut) with the statuses forgotten is t with the statuses forgotten
def at_ts.gen(+t: T.Node, +now: Nat, +cut: Bool) -> {AgentTree.unstatus(T.tick(t, now, cut)) == AgentTree.unstatus(t) : T.Node}:
  match t:
    case T.Leaf{i}:
      %Equal.sym(T.Info, AgentTree.unstatus_info(T.tick_info(Bool.or(cut, T.expired(i, now)), i)), AgentTree.unstatus_info(i), at_ts.info(Bool.or(cut, T.expired(i, now)), i)) : {T.Leaf{_} == T.Leaf{AgentTree.unstatus_info(i)} : T.Node}
      {==}
    case T.Split{i, own, l, r}:
      %Equal.sym(T.Node, AgentTree.unstatus(T.tick(l, now, Bool.or(cut, T.expired(i, now)))), AgentTree.unstatus(l), at_ts.gen(l, now, Bool.or(cut, T.expired(i, now)))) : {T.Split{AgentTree.unstatus_info(T.tick_info(Bool.or(cut, T.expired(i, now)), i)), own, _, AgentTree.unstatus(T.tick(r, now, Bool.or(cut, T.expired(i, now))))} == T.Split{AgentTree.unstatus_info(i), own, AgentTree.unstatus(l), AgentTree.unstatus(r)} : T.Node}
      %Equal.sym(T.Node, AgentTree.unstatus(T.tick(r, now, Bool.or(cut, T.expired(i, now)))), AgentTree.unstatus(r), at_ts.gen(r, now, Bool.or(cut, T.expired(i, now)))) : {T.Split{AgentTree.unstatus_info(T.tick_info(Bool.or(cut, T.expired(i, now)), i)), own, AgentTree.unstatus(l), _} == T.Split{AgentTree.unstatus_info(i), own, AgentTree.unstatus(l), AgentTree.unstatus(r)} : T.Node}
      %Equal.sym(T.Info, AgentTree.unstatus_info(T.tick_info(Bool.or(cut, T.expired(i, now)), i)), AgentTree.unstatus_info(i), at_ts.info(Bool.or(cut, T.expired(i, now)), i)) : {T.Split{_, own, AgentTree.unstatus(l), AgentTree.unstatus(r)} == T.Split{AgentTree.unstatus_info(i), own, AgentTree.unstatus(l), AgentTree.unstatus(r)} : T.Node}
      {==}

def AgentTree.agent_tree_tick_shape(b, t, now):
  at_ts.gen(t, now, False{})
