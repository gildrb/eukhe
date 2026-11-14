# eukhe: the proof of LAW agent_tree_tick_keeps_on_time
#
# PROOF: induction on the tree (E.at_edit.tick_keep): a node not late has not expired (E.at_edit.expired_false), so the tick keeps it and passes no cut down

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/edit.bend as E


def AgentTree.agent_tree_tick_keeps_on_time(b, t, now, e):
  %E.at_edit.tick_keep(t, now, e) : {T.Took{T.tick(t, now, False{})} == T.Took{_} : T.Step}
  {==}
