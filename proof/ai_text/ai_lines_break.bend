# eukhe: the proof of LAW ai_lines_break
#
# PROOF: the break read whole opens a new part (aitl.brk), and each char
# of a, no break char, joins the first part (aitl.app).

import Base
import ../../bend/ai_text.bend as T
import ../../laws/ai_text.bend as AiText
import ./base/lines.bend as LL

def AiText.ai_lines_break(a, j, b, ha, hw):
  LL.aitl.app(a, String.append(AiText.sp_brk(j), b), T.lines(b), ha, LL.aitl.brk(j, b, hw))
