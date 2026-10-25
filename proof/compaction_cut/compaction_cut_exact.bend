# eukhe: the proof of LAW compaction_cut_exact

import Base
import ../../bend/context_order.bend as Co
import ../../bend/compaction_cut.bend as Cc
import ../../laws/context_order.bend as ContextOrder
import ../../laws/compaction_cut.bend as CompactionCut
import ../context_order/base.bend as LACo
import ./base.bend as LACc

# PROOF of LAW compaction_cut_exact: where the walk stops is the spec's (cc.reach), and so are the candidates (cc.cands), the pick among them (cc.pick_cut) and the test that something comes before the cut (cc.filled).

def CompactionCut.compaction_cut_exact(head, lim, cs):
  match head:
    case True{}:
      %LACc.cc.reach(1n, lim, cs) : {Cc.cut.from(Cc.reach(1n, lim, cs), 1n, cs) == CompactionCut.cut_spec.from(_, 1n, cs) : Maybe<&2, Nat>}
      LACc.cc.cut_from(Cc.reach(1n, lim, cs), 1n, cs)
    case False{}:
      %LACc.cc.reach(0n, lim, cs) : {Cc.cut.from(Cc.reach(0n, lim, cs), 0n, cs) == CompactionCut.cut_spec.from(_, 0n, cs) : Maybe<&2, Nat>}
      LACc.cc.cut_from(Cc.reach(0n, lim, cs), 0n, cs)
