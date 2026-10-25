# eukhe: the proof of LAW cvar_tog_exact
# The lookup is the spec's (LR.re.find) and so is the value the agent
# has (LR.re.value); the flip of a Bool is the spec's, case by case.

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar.bend as Cvar
import ./base/resolve.bend as LR

def tg.flip(+x: Nat, m: Maybe<&2, Cv.Val>) -> {Cv.tog.flip(Cv.flip(x, m)) == Cvar.spec_tog.flip(x, m) : Cv.Tog}:
  match m:
    case None{}:
      {==}
    case Some{y}:
      match y:
        case Cv.VNat{n}:
          {==}
        case Cv.VBool{b}:
          {==}

def tg.value(+ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +x: Nat) -> {Cv.tog.flip(Cv.flip(x, Cv.value(ds, cfg, fam, x))) == Cvar.spec_tog.flip(x, Cvar.spec_value(ds, cfg, fam, x)) : Cv.Tog}:
  %LR.re.value(ds, cfg, fam, x) : {Cv.tog.flip(Cv.flip(x, Cv.value(ds, cfg, fam, x))) == Cvar.spec_tog.flip(x, _) : Cv.Tog}
  tg.flip(x, Cv.value(ds, cfg, fam, x))

def tg.at(m: Maybe<&2, Cv.Decl>, l: Cv.Layer, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +x: Nat) -> {Cv.tog.at(m, l, ds, cfg, fam, x) == Cvar.spec_tog.at(m, l, ds, cfg, fam, x) : Cv.Tog}:
  match m:
    case None{}:
      {==}
    case Some{d}:
      match d:
        case Cv.Decl{j, t, c, p, r, w}:
          match c:
            case Cv.Global{}:
              match l:
                case Cv.Config{}:
                  tg.value(ds, cfg, fam, x)
                case Cv.Agent{}:
                  {==}
            case Cv.Local{}:
              match l:
                case Cv.Config{}:
                  tg.value(ds, cfg, fam, x)
                case Cv.Agent{}:
                  tg.value(ds, cfg, fam, x)

def Cvar.cvar_tog_exact(ds, cfg, fam, l, x):
  %LR.re.find(ds, x) : {Cv.tog.at(Cv.find(ds, x), l, ds, cfg, fam, x) == Cvar.spec_tog.at(_, l, ds, cfg, fam, x) : Cv.Tog}
  tg.at(Cv.find(ds, x), l, ds, cfg, fam, x)
