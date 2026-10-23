# eukhe: the proof of LAW auto_never_sensitive

import Base
import ../../laws/tools.bend as Tools
import ./base.bend as LA

def Tools.auto_never_sensitive(s, auto, c, has, held):
  LA.ps.auto_never_sensitive(s, auto, c, has, held)
