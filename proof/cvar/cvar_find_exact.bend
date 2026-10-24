# eukhe: the proof of LAW cvar_find_exact
# The lookup's own test, case by case (LR.re.find).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar.bend as Cvar
import ./base/resolve.bend as LR

def Cvar.cvar_find_exact(ds, x):
  LR.re.find(ds, x)
