# eukhe: the proof of LAW cvar_tog_global
# The lookup gives the Global declaration d; in an agent layer the verdict
# asks whether d is Local: it is not.

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/resolution.bend as Cvar
import ./base.bend as LA

def tgg.go(d: Cv.Decl, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +x: Nat, global: {Cvar.spec_local(d) == False{} : Bool}) -> {Cv.tog.at(Some{d}, Cv.Agent{}, ds, cfg, fam, x) == Cv.TgGlobal{} : Cv.Tog}:
  match d:
    case Cv.Decl{j, t, c, p, r, w}:
      match c:
        case Cv.Global{}:
          {==}
        case Cv.Local{}:
          LA.pv.absurdF({Cv.tog.at(Some{Cv.Decl{j, t, Cv.Local{}, p, r, w}}, Cv.Agent{}, ds, cfg, fam, x) == Cv.TgGlobal{} : Cv.Tog}, Equal.sym(Bool, True{}, False{}, global))

def Cvar.cvar_tog_global(ds, cfg, fam, x, d, found, global):
  %Equal.sym(Maybe<&2, Cv.Decl>, Cv.find(ds, x), Some{d}, found) : {Cv.tog.at(_, Cv.Agent{}, ds, cfg, fam, x) == Cv.TgGlobal{} : Cv.Tog}
  tgg.go(d, ds, cfg, fam, x, global)
