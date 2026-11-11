# eukhe: the proof of LAW cvar_value_from_layers
# A default carried down the chain is the chain's layered value,
# defaulted (LR.rs.chain).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/resolution.bend as Cvar
import ./base/resolve.bend as LR

def Cvar.cvar_value_from_layers(ds, cfg, fam, x):
  LR.rs.value_at(Cv.find(ds, x), ds, cfg, fam, x)
