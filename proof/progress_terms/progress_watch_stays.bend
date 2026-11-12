# eukhe: the proof of LAW progress_watch_stays
#
# PROOF: by unfolding; a verdict that owes or is quiet by induction on
# the polls (pgt.watch_owe, pgt.watch_quiet).

import Base
import ../../bend/progress.bend as Pr
import ../../bend/child.bend as Ch
import ../../laws/progress_terms.bend as ProgressTerms
import ./base.bend as LPT

def ProgressTerms.progress_watch_stays(ps, cfg, hist, v, k):
  ({==}, (LPT.pgt.watch_owe(ps, cfg, hist, k), LPT.pgt.watch_quiet(ps, cfg, hist)))
