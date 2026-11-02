# eukhe: the proof of LAW ai_boundary_first
#
# PROOF: at each place before the breaks no boundary starts, so the code's
# length there is 0 and the walk goes on (aitb.zero_bnd, aitb.miss); at
# the breaks the code's length is the length of the two (aitb.eq).

import Base
import ../../laws/ai_text.bend as AiText
import ./base/boundary.bend as LB

def AiText.ai_boundary_first(a, j1, j2, r, hw1, hw2, ha):
  LB.aitb.first(a, j1, j2, r, hw1, hw2, ha)
