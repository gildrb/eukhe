# eukhe: the proof of LAW admission_background_yields

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ./base/admission/St.bend as LAAdmissionSt
import ./base/admission/calm.bend as LAAdmissionCalm
import ./base/admission/step.bend as LAAdmissionStep
import ./base/logic.bend as LALogic

def ad.okS_calm(s: Ad.St, h: {LALogic.ad.okS(s) == True{} : Bool}) -> {Ad.calm(Ad.St.ts(s)) == True{} : Bool}:
  match s:
    case Ad.St{+l, q, +ts}:
      LAAdmissionCalm.ad.calm_of(l, ts, h)

def background_yields(+l: Ad.Lim, +q: Nat, +os: List<&2, Ad.Op>) -> {Ad.calm(Ad.St.ts(Ad.run(os, Ad.St.new(l, q)))) == True{} : Bool}:
  ad.okS_calm(Ad.run(os, Ad.St.new(l, q)), LAAdmissionStep.ad.run_ok(os, Ad.St.new(l, q), LAAdmissionSt.ad.new_ok(l, q)))

def Admission.admission_background_yields(l, q, os):
  background_yields(l, q, os)
