# eukhe: the proof of LAW adw_cls_round_trip

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ../../laws/admission/wire.bend as AdmissionWire

def AdmissionWire.adw_cls_round_trip(c, rest):
  match c:
    case Ad.Ia{}:
      {==}
    case Ad.Bg{}:
      {==}

def Admission.adw_cls_round_trip(c, rest):
  match c:
    case Ad.Ia{}:
      {==}
    case Ad.Bg{}:
      {==}
