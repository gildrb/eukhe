# eukhe: the proof of LAW core_infer_left_over_spelled
#
# PROOF: the spelled request reads back whole (IS.is.run), and the end
# check sees the char left: the left-over error form.

import Base
import ../../laws/infer.bend as Infer
import ./core_infer_answers_spelled/spell.bend as IS

def Infer.core_infer_left_over_spelled(q, fits, c, t):
  IS.is.run(q, SCon{c, t}, fits)
