# eukhe: the proof of LAW compaction_cut_summary_exact

import Base
import ../../bend/context_order.bend as Co
import ../../bend/compaction_cut.bend as Cc
import ../../laws/context_order.bend as ContextOrder
import ../../laws/compaction_cut.bend as CompactionCut
import ../context_order/base.bend as LACo
import ./base.bend as LACc

# PROOF of LAW compaction_cut_summary_exact: by cases: the stop reason, then the flags and the error message the text depends on (cc.summary).

def CompactionCut.compaction_cut_summary_exact(s, calls, text, err):
  LACc.cc.summary(s, calls, text, err)
