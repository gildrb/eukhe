# eukhe: the proof of LAW model_name_segment_complete

import Base
import ../../bend/model_name.bend as M
import ../../laws/model_name.bend as ModelName
import ./base.bend as LA
import ./base/rules.bend as LR
import ./base/seg.bend as LS

# the last part of the name is p ++ b: it begins with p
def msc.got(+a: String, +p: String, +b: String, ha: {ModelName.sp_seg_start(a) == True{} : Bool}, hb: {ModelName.sp_has_slash(String.append(p, b)) == False{} : Bool}) -> {M.got(M.strip(p, M.seg(String.append(a, String.append(p, b))))) == True{} : Bool}:
  %Equal.sym(String, M.seg(String.append(a, String.append(p, b))), String.append(p, b), LS.mns.code_app(a, String.append(p, b), ha, hb)) : {M.got(M.strip(p, _)) == True{} : Bool}
  LA.mnb.got_app(p, b)

def ModelName.model_name_segment_complete(pre, p, post, a, b, ha, hb):
  LR.mnr.heads_in(pre, p, post, M.seg(String.append(a, String.append(p, b))), msc.got(a, p, b, ha, hb))
