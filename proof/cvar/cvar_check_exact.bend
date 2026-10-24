# eukhe: the proof of LAW cvar_check_exact
# The lookup is the spec's (LR.re.find); then each scope and layer, the
# type test being the spec's (LR.re.ty).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar.bend as Cvar
import ./base/resolve.bend as LR

def ck.ty(b: Bool) -> {Cv.check.ty(b) == Cvar.spec_check.ty(b) : Cv.Check}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ck.at(m: Maybe<&2, Cv.Decl>, l: Cv.Layer, +i: Nat, +v: Cv.Val) -> {Cv.check.at(m, l, Cv.Bind{i, v}) == Cvar.spec_check.at(m, l, v) : Cv.Check}:
  match m:
    case None{}:
      {==}
    case Some{d}:
      match d:
        case Cv.Decl{j, +t, c, p, r, w}:
          match c:
            case Cv.Global{}:
              match l:
                case Cv.Config{}:
                  %LR.re.ty(v, t) : {Cv.check.ty(Cv.Ty.eq(Cv.Val.ty(v), t)) == Cvar.spec_check.ty(_) : Cv.Check}
                  ck.ty(Cv.Ty.eq(Cv.Val.ty(v), t))
                case Cv.Agent{}:
                  {==}
            case Cv.Local{}:
              match l:
                case Cv.Config{}:
                  %LR.re.ty(v, t) : {Cv.check.ty(Cv.Ty.eq(Cv.Val.ty(v), t)) == Cvar.spec_check.ty(_) : Cv.Check}
                  ck.ty(Cv.Ty.eq(Cv.Val.ty(v), t))
                case Cv.Agent{}:
                  %LR.re.ty(v, t) : {Cv.check.ty(Cv.Ty.eq(Cv.Val.ty(v), t)) == Cvar.spec_check.ty(_) : Cv.Check}
                  ck.ty(Cv.Ty.eq(Cv.Val.ty(v), t))

def Cvar.cvar_check_exact(ds, l, s):
  match s:
    case Cv.Bind{+i, +v}:
      %LR.re.find(ds, i) : {Cv.check.at(Cv.find(ds, i), l, Cv.Bind{i, v}) == Cvar.spec_check.at(_, l, v) : Cv.Check}
      ck.at(Cv.find(ds, i), l, i, v)
