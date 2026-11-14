# eukhe: the proof of LAW agent_tree_parallel_is_sequential
#
# PROOF: induction on the tree generalizing the files (LP.at_patch.par_seq): the node's patch applies after its children's (seq_apply_r), each child's result stays within its scope (res_within: children's scopes lie inside the parent's by S.splits), so the overlays restrict nothing (restrict_id) and apply the subtrees in turn; apply_seq splits over List.append.

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/patch.bend as LP

def AgentTree.agent_tree_parallel_is_sequential(t, f, e):
  LP.at_patch.par_seq(t, f, e)
