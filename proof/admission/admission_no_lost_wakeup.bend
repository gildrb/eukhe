# eukhe: the proof of LAW admission_no_lost_wakeup

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ./base/admission/St.bend as LAAdmissionSt
import ./base/admission/step.bend as LAAdmissionStep
import ./base/logic.bend as LALogic

def ad.not_t(x: Bool, e: {Bool.not(x) == True{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case True{}:
      LALogic.ad.absurd({True{} == False{} : Bool}, e)
    case False{}:
      {==}

def ad.okS_quiet(s: Ad.St, h: {LALogic.ad.okS(s) == True{} : Bool}) -> {Ad.grantable(s) == False{} : Bool}:
  match s:
    case Ad.St{+l, q, +ts}:
      +g = Maybe.is_some(&2, Ad.Cls, Ad.pick(l, ts))
      ad.not_t(g, LALogic.ad.and_l(Bool.not(g), Ad.calm(ts), h))

def no_lost_wakeup(+l: Ad.Lim, +q: Nat, +os: List<&2, Ad.Op>) -> {Ad.grantable(Ad.run(os, Ad.St.new(l, q))) == False{} : Bool}:
  ad.okS_quiet(Ad.run(os, Ad.St.new(l, q)), LAAdmissionStep.ad.run_ok(os, Ad.St.new(l, q), LAAdmissionSt.ad.new_ok(l, q)))

def Admission.admission_no_lost_wakeup(l, q, os):
  no_lost_wakeup(l, q, os)
