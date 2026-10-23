# eukhe: the proof of LAW admission_live_step

import Base
import ../../laws/admission.bend as Admission
import ./base/admission/lv.bend as LAAdmissionLv

def Admission.admission_live_step(s, o):
  LAAdmissionLv.al.step(s, o)
