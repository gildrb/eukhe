# eukhe: the proof of LAW auto_needs_every_effect

import Base
import ../../laws/tools.bend as Tools
import ./base.bend as LA

def Tools.auto_needs_every_effect(s, auto, c, has, out):
  LA.ps.auto_needs_every_effect(s, auto, c, has, out)
