# eukhe: the proof of LAW core_effort_left_over_spelled
#
# PROOF: the spelled request reads back whole (ES.es.run), and the end
# check sees the char left: the left-over error form.

import Base
import ../../laws/effort.bend as Effort
import ./core_effort_answers_spelled/spell.bend as ES

def Effort.core_effort_left_over_spelled(q, fits, c, t):
  ES.es.run(q, SCon{c, t}, fits)
