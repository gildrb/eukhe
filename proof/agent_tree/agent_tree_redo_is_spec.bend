# eukhe: the proof of LAW agent_tree_redo_is_spec
#
# PROOF: the step is the edit at p through the spec's node (E.at_edit.edit_at); redoable is failed_or_cancelled_leaf, free is room and redone is regranted (E.at_edit.redo_m)

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/edit.bend as E


def AgentTree.agent_tree_redo_is_spec(b, t, p, d, x):
  %E.at_edit.edit_at(p, t, T.OpRedo{d, x}, T.bound_depth(b)) : {_ == AgentTree.redo_spec(t, p, d, x) : T.Step}
  E.at_edit.redo_m(S.node_at(p, t), t, p, d, x, T.bound_depth(b))
