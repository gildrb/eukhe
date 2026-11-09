# eukhe: the proof of LAW progress_in_only_at
#
# PROOF: by induction on the list: the act is its head (at position 0) or
# an act of its tail (pgt.only_at); mem holds only of an act (pgt.mem_in).

import Base
import ../../bend/progress.bend as Pr
import ../../bend/child.bend as Ch
import ../../laws/progress_terms.bend as ProgressTerms
import ./base.bend as LPT

def ProgressTerms.progress_in_only_at(x, xs):
  (i => LPT.pgt.only_at(x, xs, i), c => LPT.pgt.only_at(x, xs, LPT.pgt.mem_in(x, xs, c)))
