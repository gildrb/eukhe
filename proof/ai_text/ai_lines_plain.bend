# eukhe: the proof of LAW ai_lines_plain
#
# PROOF: each char, no break char, joins the one part (aitl.plain).

import Base
import ../../laws/ai_text.bend as AiText
import ./base/lines.bend as LL

def AiText.ai_lines_plain(a, ha):
  LL.aitl.plain(a, ha)
