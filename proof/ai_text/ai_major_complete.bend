# eukhe: the proof of LAW ai_major_complete
#
# PROOF: "gemini-" strips off; for the live form `live-` is no digit, so
# the second prefix strips off too; then the digits read back (aitm.digits).

import Base
import ../../bend/model_name.bend as M
import ../../bend/ai_text.bend as T
import ../../laws/ai_text.bend as AiText
import ./base/major.bend as LM

def AiText.ai_major_complete(live, d, rest, hd, hr):
  match live:
    case True{}:
      LM.aitm.digits(d, rest, hd, hr)
    case False{}:
      +y = String.append(d, rest)
      %Equal.sym(Maybe<&2, String>, T.major.digits(y), Some{d}, LM.aitm.digits(d, rest, hd, hr)) : {T.major.or(_, u => T.major.live(M.strip("live-", y))) == Some{d} : Maybe<&2, String>}
      {==}
