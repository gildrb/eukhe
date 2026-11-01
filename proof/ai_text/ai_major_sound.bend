# eukhe: the proof of LAW ai_major_sound
#
# PROOF: a stripped "gemini-" was there (mnb.sp); digits right after it
# are the answer (aitm.dig_sound); else a stripped `live-` was there and
# the digits after it are the answer.

import Base
import ../../bend/model_name.bend as M
import ../../laws/ai_text.bend as AiText
import ../model_name/base.bend as LA
import ./base/major.bend as LM

def AiText.ai_major_sound(id, d, h):
  LM.aitm.s1(id, d, M.strip("gemini-", id), LA.mnb.sp("gemini-", id), h)
