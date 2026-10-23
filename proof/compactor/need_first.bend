# eukhe: the proof of LAW need_first

import Base
import ../../LAWS.bend as Laws
import ./base.bend as LA

# (H2) A turn never waits forever for the memory

def Laws.need_first(cfg, s):
  LA.pc.need_first(cfg, s)
