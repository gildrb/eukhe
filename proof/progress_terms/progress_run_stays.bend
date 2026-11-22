# eukhe: the proof of LAW progress_run_stays
#
# PROOF: by unfolding; a stopped run by cases on the continuations
# (pgt.run_stop).

import Base
import ../../bend/progress.bend as Pr
import ../../bend/child.bend as Ch
import ../../laws/progress_terms.bend as ProgressTerms
import ./base.bend as LPT

def ProgressTerms.progress_run_stays(segs, cap, hist, g, s):
  ({==}, LPT.pgt.run_stop(segs, cap, hist, s))
