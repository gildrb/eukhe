# eukhe: the proof of LAW adw_step_exact
# The stepper reads the op as the spec reads it (LE.pae.get_op); the live
# controller steps as the model does on the state it holds
# (admission_live_step), the model as the spec (admission_step_exact), and
# the reply is spelled as the spec spells it (LE.pae.live).

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission.bend as Admission
import ../../laws/admission/entry.bend as AdmissionEntry
import ./base/entry.bend as LE
import ./admission_live_step.bend as PLS
import ./admission_step_exact.bend as PSE

def pase.end(b: Bool, +st: Ad.St, +o: Ad.Op) -> {FAd.step.end(b, Admission.adl_live(st), o) == AdmissionEntry.ads_stepper.end(b, st, o) : FAd.St & String}:
  match b:
    case True{}:
      +y = Ad.Live.step(Admission.adl_live(st), o)
      %Admission.admission_step_exact(st, o) : {(FAd.Running{y}, FAd.put_live(y, "")) == (FAd.Running{Admission.adl_live(_)}, AdmissionEntry.ads_spell_live(Admission.adl_live(_), "")) : FAd.St & String}
      %Admission.admission_live_step(st, o) : {(FAd.Running{y}, FAd.put_live(y, "")) == (FAd.Running{_}, AdmissionEntry.ads_spell_live(_, "")) : FAd.St & String}
      %LE.pae.live(y, "") : {(FAd.Running{y}, FAd.put_live(y, "")) == (FAd.Running{y}, _) : FAd.St & String}
      {==}
    case False{}:
      {==}

def pase.op(+st: Ad.St, d: Wr.Dec<Ad.Op>) -> {FAd.step.op(Admission.adl_live(st), d) == AdmissionEntry.ads_stepper.go(st, d) : FAd.St & String}:
  match d:
    case Wr.Got{o, s}:
      pase.end(Wr.end(s), st, o)
    case Wr.Bad{}:
      {==}

def AdmissionEntry.adw_step_exact(st, s):
  %LE.pae.get_op(s) : {FAd.step.op(Admission.adl_live(st), FAd.get_op(s)) == AdmissionEntry.ads_stepper.go(st, _) : FAd.St & String}
  pase.op(st, FAd.get_op(s))
