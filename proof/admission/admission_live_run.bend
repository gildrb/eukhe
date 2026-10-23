# eukhe: the proof of LAW admission_live_run

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ./base/admission/lv.bend as LAAdmissionLv

def al.run(os: List<&2, Ad.Op>, +t: Ad.St) -> {Ad.Live.run(os, Admission.adl_live(t)) == Admission.adl_live(Ad.run(os, t)) : Ad.Live}:
  match os:
    case Nil{}:
      {==}
    case +o <> r:
      %Equal.sym(Ad.Live, Ad.Live.step(Admission.adl_live(t), o), Admission.adl_live(Ad.step(t, o)), LAAdmissionLv.al.step(t, o)) : {Ad.Live.run(r, _) == Admission.adl_live(Ad.run(r, Ad.step(t, o))) : Ad.Live}
      al.run(r, Ad.step(t, o))

def Admission.admission_live_run(l, q, os):
  al.run(os, Ad.St.new(l, q))
