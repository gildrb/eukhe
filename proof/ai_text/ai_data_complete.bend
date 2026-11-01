# eukhe: the proof of LAW ai_data_complete
#
# PROOF: the chunks are one pass over the text they make (aitr.chunks);
# that text is the data URL, which runs to the data state with its mime's
# length (aitr.data_run).

import Base
import ../../bend/ai_text.bend as T
import ../../laws/ai_text.bend as AiText
import ./base/data.bend as LR

def AiText.ai_data_complete(cs, m, d, hc, hm, hd):
  +p0 = {T.DPre{"data:"} : T.Du}
  +c = AiText.sp_cat(cs)
  +u = AiText.sp_data(m, d)
  +f = {T.DData{String.length(m), True{}} : T.Du}
  Equal.cong(T.Du, Maybe<&2, Nat>, z => T.du.verdict(z), T.du.chunks(cs, p0), f, Equal.trans(T.Du, T.du.chunks(cs, p0), T.du.go(c, p0), f, LR.aitr.chunks(cs, p0), Equal.trans(T.Du, T.du.go(c, p0), T.du.go(u, p0), f, Equal.cong(String, T.Du, z => T.du.go(z, p0), c, u, hc), LR.aitr.data_run(m, d, hm, hd))))
