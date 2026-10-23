# eukhe: the proof of LAW adw_step_answers

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.adw_step_answers(x, o, h):
  %LA.paw.op(o, "", h) : {FAd.step.op(x, _) == (FAd.Running{Ad.Live.step(x, o)}, FAd.put_live(Ad.Live.step(x, o), "")) : FAd.St & String}
  {==}
