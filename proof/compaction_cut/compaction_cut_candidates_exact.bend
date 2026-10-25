# eukhe: the proof of LAW compaction_cut_candidates_exact

import Base
import ../../bend/context_order.bend as Co
import ../../bend/compaction_cut.bend as Cc
import ../../laws/context_order.bend as ContextOrder
import ../../laws/compaction_cut.bend as CompactionCut
import ../context_order/base.bend as LACo
import ./base.bend as LACc

# PROOF of LAW compaction_cut_candidates_exact: the code carries the calls of the last assistant answer before each contribution, which are the spec's (cc.step_calls), and its candidate test is the spec's (cc.cand: its look ahead is the spec's scan, cc.ahead).

def CompactionCut.compaction_cut_candidates_exact(start, cs):
  LACc.cc.cands(cs, [], 0n, start)
