# eukhe: the proof of LAW ai_boundary_none
#
# PROOF: no boundary at any place: the code's length is 0 at each place
# (aitb.zero_bnd), so the walk reaches the end and answers none.

import Base
import ../../laws/ai_text.bend as AiText
import ./base/boundary.bend as LB

def AiText.ai_boundary_none(s, h):
  LB.aitb.none(s, h)
