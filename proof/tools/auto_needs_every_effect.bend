# eukhe: the proof of LAW auto_needs_every_effect

import Base
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.auto_needs_every_effect(s, auto, c, has, out):
  LA.ps.auto_needs_every_effect(s, auto, c, has, out)
