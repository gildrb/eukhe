# eukhe: the proof of LAW cvar_tog_not_bool
# A declared cvar (an undeclared one has no value) the layer allows: the
# verdict flips the value (LV.tg.allowed), a Nat: not a Bool.

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/resolution.bend as Cvar
import ./base/verdict.bend as LV

def Cvar.cvar_tog_not_bool(ds, cfg, fam, l, x, n, allowed, val):
  LV.tg.allowed(Cv.find(ds, x), l, ds, cfg, fam, x, Cv.VNat{n}, {==}, allowed, val)
