# eukhe: the proof of LAW admission_live_step

import Base
import ../../laws/admission.bend as Admission
import ./base.bend as LA

def Admission.admission_live_step(s, o):
  LA.al.step(s, o)
