# eukhe: the proof of LAW cvar_layered_exact
# Each layer is the spec's last set that counts (LR.re.layer), down the
# family chain (LR.re.chainm).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar.bend as Cvar
import ./base/resolve.bend as LR

def Cvar.cvar_layered_exact(ds, cfg, fam, x):
  LR.re.layered(ds, cfg, fam, x)
