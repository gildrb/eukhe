# eukhe: the proof of LAW crown_free_is_spec
#
# PROOF: the code's view and node lookup are the spec's (base/view.bend);
# the code's free of a node is the spec's room (agent_tree's
# at_edit.room_free).

import Base
import ../../bend/agent_tree.bend as T
import ../../bend/agent_crown.bend as A
import ../../spec/agents/agent_tree.bend as S
import ../../spec/agents/agent_crown.bend as CS
import ../../laws/agent_tree.bend as AgentTree
import ../../laws/agent_crown.bend as AgentCrown
import ../agent_tree/base/edit.bend as E
import ./base/view.bend as V

def ac_free.free_room(+m: Maybe<&2, T.Node>) -> {A.free_of(m) == AgentCrown.room_at(m) : Maybe<&2, T.Lim>}:
  match m:
    case None{}:
      {==}
    case Some{+n}:
      Equal.cong(T.Lim, Maybe<&2, T.Lim>, z => Some{z}, T.free(n), S.room(n), Equal.sym(T.Lim, S.room(n), T.free(n), E.at_edit.room_free(n)))

def ac_free.at(+t: T.Node, +hs: List<&2, A.Help>, +p: List<&2, T.Dir>) -> {A.cfree(A.Crown{t, hs}, p) == AgentCrown.room_at(S.node_at(p, CS.view(A.Crown{t, hs}))) : Maybe<&2, T.Lim>}:
  %V.ac_view.view_eq(t, hs) : {A.free_of(A.node_at(p, A.view(t, hs))) == AgentCrown.room_at(S.node_at(p, _)) : Maybe<&2, T.Lim>}
  %V.ac_view.node_at_eq(p, A.view(t, hs)) : {A.free_of(A.node_at(p, A.view(t, hs))) == AgentCrown.room_at(_) : Maybe<&2, T.Lim>}
  ac_free.free_room(A.node_at(p, A.view(t, hs)))

def AgentCrown.crown_free_is_spec(c, p):
  match c:
    case A.Crown{t, hs}:
      ac_free.at(t, hs, p)
