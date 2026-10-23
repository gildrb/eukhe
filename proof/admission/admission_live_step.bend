# eukhe: the proof of LAW admission_live_step

import Base
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.admission_live_step(s, o):
  LA.al.step(s, o)
