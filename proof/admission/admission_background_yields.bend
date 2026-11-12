# eukhe: the proof of LAW admission_background_yields

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ./base/admission/St.bend as LAAdmissionSt
import ./base/admission/calm.bend as LAAdmissionCalm
import ./base/admission/step.bend as LAAdmissionStep
import ./base/logic.bend as LALogic
import ./base/admission/terms.bend as AT
import ./base/admission/bridge.bend as LBr

def ad.okS_calm(s: Ad.St, h: {LALogic.ad.okS(s) == True{} : Bool}) -> {AT.calm(Admission.adm_ts(s)) == True{} : Bool}:
  match s:
    case Ad.St{+l, q, +ts}:
      LAAdmissionCalm.ad.calm_of(l, ts, h)

def background_yields(+l: Ad.Lim, +q: Nat, +os: List<&2, Ad.Op>) -> {AT.calm(Admission.adm_ts(Admission.adm_run(os, AT.St.new(l, q)))) == True{} : Bool}:
  ad.okS_calm(Admission.adm_run(os, AT.St.new(l, q)), LAAdmissionStep.ad.run_ok(os, AT.St.new(l, q), LAAdmissionSt.ad.new_ok(l, q)))

def Admission.admission_background_yields(l, q, os):
  %LBr.br.calm(Admission.adm_ts(Admission.adm_run(os, Ad.St{l, q, Nil{}}))) : {_ == True{} : Bool}
  background_yields(l, q, os)
