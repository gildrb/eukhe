# eukhe: the proof of LAW wfw_left_over_spelled
#
# PROOF: the spelled request reads back whole (sp.ffi), whose end check
# sees the char left and answers the error form.

import Base
import ../../laws/workflow.bend as Workflow
import ./wfw_answers_spelled/spell.bend as SP

def Workflow.wfw_left_over_spelled(q, fits, c, rest):
  SP.sp.ffi(q, SCon{c, rest}, fits)
