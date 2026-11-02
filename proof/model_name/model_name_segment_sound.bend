# eukhe: the proof of LAW model_name_segment_sound

import Base
import ../../bend/model_name.bend as M
import ../../laws/model_name.bend as ModelName
import ./base.bend as LA
import ./base/rules.bend as LR
import ./base/decide.bend as LD
import ./base/seg.bend as LS

def mss.G(ps: List<&2, String>, s: String) -> Type:
  Sigma<&1, &1, List<&2, String>, pre => Sigma<&1, &1, String, p => Sigma<&1, &1, List<&2, String>, post => Sigma<&1, &1, String, a => Sigma<&1, &1, String, b => {ps == List.append(&2, String, pre, p <> post) : List<&2, String>} & ({s == String.append(a, String.append(p, b)) : String} & ({ModelName.sp_seg_start(a) == True{} : Bool} & {ModelName.sp_has_slash(String.append(p, b)) == False{} : Bool}))>>>>>

def mss.join(+ps: List<&2, String>, +s: String, +pre: List<&2, String>, +p: String, +post: List<&2, String>, +c: String, e1: {ps == List.append(&2, String, pre, p <> post) : List<&2, String>}, e2: {M.seg(s) == String.append(p, c) : String}, q: LS.mns.SegQ(s, ModelName.sp_seg(s))) -> mss.G(ps, s):
  (+a, (es, (st, nh))) = q
  +e3 = Equal.trans(String, ModelName.sp_seg(s), M.seg(s), String.append(p, c), Equal.sym(String, M.seg(s), ModelName.sp_seg(s), LD.mnd.seg(s)), e2)
  +e4 = Equal.trans(String, s, String.append(a, ModelName.sp_seg(s)), String.append(a, String.append(p, c)), es, Equal.cong(String, String, z => String.append(a, z), ModelName.sp_seg(s), String.append(p, c), e3))
  +e5 = Equal.trans(Bool, ModelName.sp_has_slash(String.append(p, c)), ModelName.sp_has_slash(ModelName.sp_seg(s)), False{}, Equal.cong(String, Bool, z => ModelName.sp_has_slash(z), String.append(p, c), ModelName.sp_seg(s), Equal.sym(String, ModelName.sp_seg(s), String.append(p, c), e3)), nh)
  (pre, (p, (post, (a, (c, (e1, (e4, (st, e5))))))))

def mss.fin(+ps: List<&2, String>, +s: String, hp: LR.mnr.HeadsP(ps, M.seg(s), True{})) -> mss.G(ps, s):
  (+pre, (+p, (+post, (+c, (e1, e2))))) = hp
  mss.join(ps, s, pre, p, post, c, e1, e2, LS.mns.split(s))

def mss.at(+ps: List<&2, String>, +s: String, b: Bool, hp: LR.mnr.HeadsP(ps, M.seg(s), b), eb: {b == True{} : Bool}) -> mss.G(ps, s):
  match b:
    case True{}:
      mss.fin(ps, s, hp)
    case False{}:
      LA.mnb.absurd_f(mss.G(ps, s), eb)

def ModelName.model_name_segment_sound(ps, s, h):
  mss.at(ps, s, M.heads(ps, M.seg(s)), LR.mnr.heads_sp(ps, M.seg(s)), h)
