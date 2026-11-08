# eukhe: the proof of LAW cvar_registry_exact
# The model folds declare onto the kept declarations; the spec, its pick.
# An id is taken in the kept ones exactly when it is one of their ids
# (LR.re.mem), the type test is the spec's (LR.re.ty), and declare's
# choice is the spec's pick, case by case (rg.at).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/resolution.bend as Cvar
import ../../laws/cvar/whole.bend as CvarWhole
import ./base/resolve.bend as LR

# declare keeps or grows the kept ones as the spec's pick does
def rg.at(taken: Bool, good: Bool, +ds: List<&2, Cv.Decl>, +d: Cv.Decl) -> {Cv.declare.at(taken, good, ds, d) == CvarWhole.spec_registry.pick(taken, good, ds, d) : List<&2, Cv.Decl>}:
  match taken:
    case True{}:
      {==}
    case False{}:
      match good:
        case True{}:
          {==}
        case False{}:
          {==}

# the fold onto the kept ds is the spec's fold onto ds
def rg.go(xs: List<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>) -> {Cv.registry.go(xs, ds) == CvarWhole.spec_registry(xs, ds) : List<&2, Cv.Decl>}:
  match xs:
    case Nil{}:
      {==}
    case Cv.Decl{+i, +t, +c, +p, +r, +v} <> +rest:
      +d = {Cv.Decl{i, t, c, p, r, v} : Cv.Decl}
      +k = Cv.declare(ds, d)
      %LR.re.mem(ds, i) : {Cv.registry.go(rest, k) == CvarWhole.spec_registry(rest, CvarWhole.spec_registry.pick(_, Cvar.spec_typed(v, t), ds, d)) : List<&2, Cv.Decl>}
      %LR.re.ty(v, t) : {Cv.registry.go(rest, k) == CvarWhole.spec_registry(rest, CvarWhole.spec_registry.pick(Maybe.is_some(&2, Cv.Decl, Cv.find(ds, i)), _, ds, d)) : List<&2, Cv.Decl>}
      %rg.at(Maybe.is_some(&2, Cv.Decl, Cv.find(ds, i)), Cv.Ty.eq(Cv.Val.ty(v), t), ds, d) : {Cv.registry.go(rest, k) == CvarWhole.spec_registry(rest, _) : List<&2, Cv.Decl>}
      rg.go(rest, k)

def CvarWhole.cvar_registry_exact(xs):
  rg.go(xs, Nil{})
