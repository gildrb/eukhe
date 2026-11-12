# eukhe: the proof of LAW cvar_find_absent
# Induction on ds: every declaration has another id, so the lookup passes
# each one and ends with none (LR.rs.find_absent).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/resolution.bend as Cvar
import ./base/resolve.bend as LR

def Cvar.cvar_find_absent(ds, x, none):
  LR.rs.find_absent(ds, x, none)
