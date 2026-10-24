# eukhe: the proof of LAW cvar_value_exact
# A default carried down the chain is the chain's layered value,
# defaulted (LR.re.chain), and that layered value is the spec's.

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar.bend as Cvar
import ./base/resolve.bend as LR

def Cvar.cvar_value_exact(ds, cfg, fam, x):
  LR.re.value(ds, cfg, fam, x)
