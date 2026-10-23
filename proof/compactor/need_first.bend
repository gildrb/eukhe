# eukhe: the proof of LAW need_first

import Base
import ../../laws/compactor.bend as Compactor
import ./base.bend as LA

# (H2) A turn never waits forever for the memory

def Compactor.need_first(cfg, s):
  LA.pc.need_first(cfg, s)
