# eukhe: the proof of LAW progress_goal_stays
#
# PROOF: by unfolding; a stopped goal by cases on the continuations
# (pgt.goal_stop).

import Base
import ../../bend/progress.bend as Pr
import ../../bend/child.bend as Ch
import ../../laws/progress_terms.bend as ProgressTerms
import ./base.bend as LPT

def ProgressTerms.progress_goal_stays(segs, cap, hist, g, s):
  ({==}, LPT.pgt.goal_stop(segs, cap, hist, s))
