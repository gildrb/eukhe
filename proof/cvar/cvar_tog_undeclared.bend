# eukhe: the proof of LAW cvar_tog_undeclared
# The lookup gives none: the verdict's first case.

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/resolution.bend as Cvar

def Cvar.cvar_tog_undeclared(ds, cfg, fam, l, x, none):
  %Equal.sym(Maybe<&2, Cv.Decl>, Cv.find(ds, x), None{}, none) : {Cv.tog.at(_, l, ds, cfg, fam, x) == Cv.TgUndeclared{} : Cv.Tog}
  {==}
