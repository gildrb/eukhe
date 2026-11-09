# eukhe: the proof of LAW admission_live_run

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ./base/admission/lv.bend as LAAdmissionLv

def al.run(os: List<&2, Ad.Op>, +t: Ad.St) -> {Admission.adl_run(os, Admission.adl_live(t)) == Admission.adl_live(Admission.adm_run(os, t)) : Ad.Live}:
  match os:
    case Nil{}:
      {==}
    case +o <> r:
      %Equal.sym(Ad.Live, Ad.Live.step(Admission.adl_live(t), o), Admission.adl_live(Ad.step(t, o)), LAAdmissionLv.al.step(t, o)) : {Admission.adl_run(r, _) == Admission.adl_live(Admission.adm_run(r, Ad.step(t, o))) : Ad.Live}
      al.run(r, Ad.step(t, o))

def Admission.admission_live_run(os, s):
  al.run(os, s)
