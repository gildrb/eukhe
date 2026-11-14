# eukhe: the proof of LAW agent_tree_entry_reads
#
# PROOF: field by field, each decoder reads its spelling back; a node by
# induction on it, its fuel (the length of its input) at least its need
# (ate.reads).

import Base
import ../../bend/agent_tree.bend as T
import ../../bend/ffi_agent_tree.bend as FAt
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/agent_tree.bend as AgentTree
import ./base/entry.bend as ATE

def AgentTree.agent_tree_entry_reads(q, rest, fit):
  ATE.ate.reads(q, rest, fit)
