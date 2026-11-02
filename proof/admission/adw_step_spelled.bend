# eukhe: the proof of LAW adw_step_spelled
# The spec's spelling is the entry's encoding (LE.pae.op), which steps the
# live controller (adw_step_answers) as the model and the spec do.

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission.bend as Admission
import ./base/entry.bend as LE
import ./adw_step_answers.bend as PSA
import ./admission_live_step.bend as PLS
import ./admission_step_exact.bend as PSE

def Admission.adw_step_spelled(st, o, h):
  +x = Admission.adl_live(st)
  +y = Ad.Live.step(x, o)
  %LE.pae.op(o, "") : {FAd.step(FAd.Running{x}, _) == (FAd.Running{Admission.adl_live(Admission.ads_step(st, o))}, Admission.ads_spell_live(Admission.adl_live(Admission.ads_step(st, o)), "")) : FAd.St & String}
  %Equal.sym(FAd.St & String, FAd.step(FAd.Running{x}, FAd.put_op(o, "")), (FAd.Running{y}, FAd.put_live(y, "")), Admission.adw_step_answers(x, o, h)) : {_ == (FAd.Running{Admission.adl_live(Admission.ads_step(st, o))}, Admission.ads_spell_live(Admission.adl_live(Admission.ads_step(st, o)), "")) : FAd.St & String}
  %Admission.admission_step_exact(st, o) : {(FAd.Running{y}, FAd.put_live(y, "")) == (FAd.Running{Admission.adl_live(_)}, Admission.ads_spell_live(Admission.adl_live(_), "")) : FAd.St & String}
  %Admission.admission_live_step(st, o) : {(FAd.Running{y}, FAd.put_live(y, "")) == (FAd.Running{_}, Admission.ads_spell_live(_, "")) : FAd.St & String}
  %LE.pae.live(y, "") : {(FAd.Running{y}, FAd.put_live(y, "")) == (FAd.Running{y}, _) : FAd.St & String}
  {==}
