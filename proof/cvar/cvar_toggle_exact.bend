# eukhe: the proof of LAW cvar_toggle_exact
# The value the agent has is the spec's (LR.re.value); the set a toggle
# adds is the one the spec's verdict names, case by case on the value
# (tt.flip); an undeclared cvar has no value, so nothing is added (tt.at).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/resolution.bend as Cvar
import ../../laws/cvar/whole.bend as CvarWhole
import ./base/resolve.bend as LR

# the set a flip of v adds is the one the spec's verdict on v names
def tt.flip(a: Cv.Ag, +x: Nat, v: Maybe<&2, Cv.Val>) -> {Cv.add(a, Cv.flip(x, v)) == CvarWhole.spec_tog_apply(a, Cvar.spec_tog.flip(x, v)) : Cv.Ag}:
  match a:
    case Cv.Ag{p, ss}:
      match v:
        case None{}:
          {==}
        case Some{y}:
          match y:
            case Cv.VNat{n}:
              {==}
            case Cv.VBool{b}:
              {==}

# by the declaration of x: none adds nothing, one adds the flip
def tt.at(m: Maybe<&2, Cv.Decl>, a: Cv.Ag, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +x: Nat, e: {Cvar.spec_find(ds, x) == m : Maybe<&2, Cv.Decl>}) -> {Cv.add(a, Cv.flip(x, Cvar.spec_value(ds, cfg, fam, x))) == CvarWhole.spec_tog_apply(a, Cvar.spec_tog.at(m, Cv.Config{}, ds, cfg, fam, x)) : Cv.Ag}:
  match m:
    case None{}:
      match a:
        case Cv.Ag{p, ss}:
          %Equal.sym(Maybe<&2, Cv.Decl>, Cvar.spec_find(ds, x), None{}, e) : {Cv.add(Cv.Ag{p, ss}, Cv.flip(x, Cvar.spec_value.at(_, Cvar.spec_layered(ds, cfg, fam, x)))) == Cv.Ag{p, ss} : Cv.Ag}
          {==}
    case Some{d}:
      tt.flip(a, x, Cvar.spec_value(ds, cfg, fam, x))

def CvarWhole.cvar_toggle_exact(ds, cfg, fam, a, x):
  +fa = List.append(&2, Cv.Ag, fam, [a])
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.value(ds, cfg, fa, x), Cvar.spec_value(ds, cfg, fa, x), LR.re.value(ds, cfg, fa, x)) : {Cv.add(a, Cv.flip(x, _)) == CvarWhole.spec_tog_apply(a, Cvar.spec_tog(ds, cfg, fa, Cv.Config{}, x)) : Cv.Ag}
  tt.at(Cvar.spec_find(ds, x), a, ds, cfg, fa, x, {==})
