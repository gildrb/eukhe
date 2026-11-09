# eukhe: the proof of LAW progress_in_at
#
# PROOF: by induction on the acts before the position (pgt.in_at, pgt.mem_at).

import Base
import ../../bend/progress.bend as Pr
import ../../bend/child.bend as Ch
import ../../laws/progress_terms.bend as ProgressTerms
import ./base.bend as LPT

def ProgressTerms.progress_in_at(a, x, b):
  (LPT.pgt.in_at(a, x, b), LPT.pgt.mem_at(a, x, b))
