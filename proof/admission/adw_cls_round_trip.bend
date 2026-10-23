# eukhe: the proof of LAW adw_cls_round_trip

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission

def Admission.adw_cls_round_trip(c, rest):
  match c:
    case Ad.Ia{}:
      {==}
    case Ad.Bg{}:
      {==}
