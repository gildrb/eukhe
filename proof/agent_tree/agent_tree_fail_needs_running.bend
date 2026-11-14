# eukhe: the proof of LAW agent_tree_fail_needs_running
#
# PROOF: the fail is local at the spec's node (E.at_edit.edit_at), which refuses NotRunning when it does not run (E.at_edit.fail_nr)

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/edit.bend as E


def AgentTree.agent_tree_fail_needs_running(b, t, p, q, n, e, r):
  %E.at_edit.edit_at(p, t, T.OpFail{q}, T.bound_depth(b)) : {_ == T.Refused{T.NotRunning{}} : T.Step}
  E.at_edit.fail_nr(p, t, q, n, T.bound_depth(b), e, r)
