# eukhe: the proof of LAW cvar_check_fine
# The one set alone in its layer is that layer (no family, or one agent
# with no profile); its value is set exactly when it is a set of its own
# id that counts (LR.rs.one), and the verdict is valid exactly when it
# counts (LV.ck.fine_at).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/resolution.bend as Cvar
import ./base.bend as LA
import ./base/resolve.bend as LR
import ./base/verdict.bend as LV

def ckf.go(+ds: List<&2, Cv.Decl>, +l: Cv.Layer, +i: Nat, +v: Cv.Val) -> {Cvar.spec_ck_fine(Cv.check(ds, l, Cv.Bind{i, v})) == Maybe.is_some(&2, Cv.Val, Cv.layer([Cv.Bind{i, v}], ds, l, i, None{})) : Bool}:
  +b = {Cv.Bind{i, v} : Cv.Bind}
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer([b], ds, l, i, None{}), Cvar.spec_latest(Cvar.spec_tag(l, [b]), ds, i), LR.rs.one(b, ds, l, i)) : {Cvar.spec_ck_fine(Cv.check(ds, l, b)) == Maybe.is_some(&2, Cv.Val, _) : Bool}
  %LA.cvar.pv.eq_refl(i) : {Cvar.spec_ck_fine(Cv.check(ds, l, b)) == Maybe.is_some(&2, Cv.Val, Cvar.spec_latest.or(None{}, Bool.and(_, Cvar.spec_counts(ds, l, b)), v)) : Bool}
  %Equal.sym(Bool, Maybe.is_some(&2, Cv.Val, Cvar.spec_latest.or(None{}, Cvar.spec_counts(ds, l, b), v)), Cvar.spec_counts(ds, l, b), LV.ck.some_or(Cvar.spec_counts(ds, l, b), v)) : {Cvar.spec_ck_fine(Cv.check(ds, l, b)) == _ : Bool}
  LV.ck.fine_at(Cv.find(ds, i), l, i, v)

def Cvar.cvar_check_fine(ds, l, s):
  match l:
    case Cv.Config{}:
      match s:
        case Cv.Bind{+i, +v}:
          ckf.go(ds, Cv.Config{}, i, v)
    case Cv.Agent{}:
      match s:
        case Cv.Bind{+i, +v}:
          ckf.go(ds, Cv.Agent{}, i, v)
