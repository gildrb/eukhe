# eukhe: the proof of LAW cvar_refusal_first_drop
# pre is kept whole (LW.wh.ref); at d the refusal asks whether d's id is
# declared in pre (not spec_no_id, LR.rs.some_no_id) and whether its
# default has its type (LW.wh.typed); d is dropped, so one fails
# (LW.wh.reason).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/resolution.bend as Cvar
import ../../laws/cvar/whole.bend as CvarWhole
import ./base/resolve.bend as LR
import ./base/whole.bend as LW

def rfd.go(+pre: List<&2, Cv.Decl>, d: Cv.Decl, +post: List<&2, Cv.Decl>, drop: {Bool.and(Cvar.spec_no_id(pre, Cvar.spec_id(d)), Cvar.spec_good(d)) == False{} : Bool}) -> {Cv.refusal.go(d <> post, pre, Maybe.is_some(&2, Cv.Decl, Cv.find(pre, Cv.Decl.id(d))), Cv.Decl.typed(d)) == CvarWhole.spec_reason(Cvar.spec_no_id(pre, Cvar.spec_id(d)), Cvar.spec_id(d)) : Cv.Refusal}:
  match d:
    case Cv.Decl{+i, +t, +c, +q, +r, +v}:
      %Equal.sym(Bool, Maybe.is_some(&2, Cv.Decl, Cv.find(pre, i)), Bool.not(Cvar.spec_no_id(pre, i)), LR.rs.some_no_id(pre, i)) : {Cv.refusal.go(Cv.Decl{i, t, c, q, r, v} <> post, pre, _, Cv.Ty.eq(Cv.Val.ty(v), t)) == CvarWhole.spec_reason(Cvar.spec_no_id(pre, i), i) : Cv.Refusal}
      %Equal.sym(Bool, Cv.Ty.eq(Cv.Val.ty(v), t), Cvar.spec_typed(v, t), LR.rs.ty_eq(v, t)) : {Cv.refusal.go(Cv.Decl{i, t, c, q, r, v} <> post, pre, Bool.not(Cvar.spec_no_id(pre, i)), _) == CvarWhole.spec_reason(Cvar.spec_no_id(pre, i), i) : Cv.Refusal}
      LW.wh.reason(Cvar.spec_no_id(pre, i), Cvar.spec_typed(v, t), i, t, c, q, r, v, post, pre, drop)

def CvarWhole.cvar_refusal_first_drop(pre, d, post, whole, drop):
  Equal.trans(Cv.Refusal, Cv.refusal(List.append(&2, Cv.Decl, pre, d <> post)), Cv.refusal.go(d <> post, pre, Maybe.is_some(&2, Cv.Decl, Cv.find(pre, Cv.Decl.id(d))), Cv.Decl.typed(d)), CvarWhole.spec_reason(Cvar.spec_no_id(pre, Cvar.spec_id(d)), Cvar.spec_id(d)),
    LW.wh.ref(pre, Nil{}, d <> post, whole, LW.wh.fresh_nil(pre)),
    rfd.go(pre, d, post, drop))
