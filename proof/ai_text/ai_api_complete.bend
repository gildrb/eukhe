# eukhe: the proof of LAW ai_api_complete
#
# PROOF: the walk over a reaches the part with the start flag True
# (aita.walk, the place ends with `/` or is the start), and the part is a
# version (aita.ver_ok, aita.go_here).

import Base
import ../../bend/ai_text.bend as T
import ../../laws/ai_text.bend as AiText
import ./base/api.bend as LP

def AiText.ai_api_complete(a, d, m, b, ha, hd, hm, hb):
  +u = String.append("v", String.append(d, String.append(AiText.sp_beta(m), b)))
  +g = LP.aita.go_here(u, LP.aita.ver_ok(d, m, b, hd, hm, hb))
  LP.aita.walk(a, u, True{}, Equal.trans(Bool, T.api.go(u, AiText.sp_last_slash(a, True{})), T.api.go(u, True{}), True{}, Equal.cong(Bool, Bool, z => T.api.go(u, z), AiText.sp_last_slash(a, True{}), True{}, ha), g))
