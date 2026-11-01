# eukhe: the proof of LAW ai_data_sound
#
# PROOF: the chunks are one pass over the text they make (aitr.chunks);
# what the reading accepts from its start is a data URL whose mime has the
# answered length (aitr.sound: prefix, mime, mark, data states in turn).

import Base
import ../../bend/ai_text.bend as T
import ../../laws/ai_text.bend as AiText
import ./base/data.bend as LR

def AiText.ai_data_sound(cs, n, h):
  +p0 = {T.DPre{"data:"} : T.Du}
  +c = AiText.sp_cat(cs)
  LR.aitr.sound(c, n, Equal.trans(Maybe<&2, Nat>, T.du.verdict(T.du.go(c, p0)), T.du.verdict(T.du.chunks(cs, p0)), Some{n}, Equal.cong(T.Du, Maybe<&2, Nat>, z => T.du.verdict(z), T.du.go(c, p0), T.du.chunks(cs, p0), Equal.sym(T.Du, T.du.chunks(cs, p0), T.du.go(c, p0), LR.aitr.chunks(cs, p0))), h))
