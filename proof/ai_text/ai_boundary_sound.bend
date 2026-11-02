# eukhe: the proof of LAW ai_boundary_sound
#
# PROOF: the walk answers the first place where the code's length is not
# 0 (aitb.sound); there the length is two breaks read whole
# (aitb.bnd_sound), and before it no boundary starts (aitb.zero_bnd).

import Base
import ../../laws/ai_text.bend as AiText
import ./base/boundary.bend as LB

def AiText.ai_boundary_sound(s, i, l, h):
  LB.aitb.fin_law(s, i, l, LB.aitb.sound(s, i, l, h))
