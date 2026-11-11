# eukhe: the proof of LAW orphan_step_spec

import Base
import ../../laws/orphan.bend as Orphan
import ./base.bend as LA

def Orphan.orphan_step_spec(window, s, e):
  LA.ps.ow_step(window, s, e)
