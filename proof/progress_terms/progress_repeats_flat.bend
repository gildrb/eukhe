# eukhe: the proof of LAW progress_repeats_flat
#
# PROOF: by induction on the segments (polls), splitting and joining the
# runs of acts (pgt.repeats_flat, pgt.flat_repeats, pgt.loops_flat,
# pgt.flat_loops).

import Base
import ../../bend/progress.bend as Pr
import ../../bend/child.bend as Ch
import ../../laws/progress_terms.bend as ProgressTerms
import ./base.bend as LPT

def ProgressTerms.progress_repeats_flat(segs, ps, hist):
  ((r => LPT.pgt.repeats_flat(segs, hist, r), w => LPT.pgt.flat_repeats(segs, hist, w)), (l => LPT.pgt.loops_flat(ps, hist, l), w => LPT.pgt.flat_loops(ps, hist, w)))
