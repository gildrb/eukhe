# eukhe: the proof of LAW adw_step_answers

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../laws/admission.bend as Admission
import ./base/wire.bend as LAWire

def Admission.adw_step_answers(x, o, h):
  %LAWire.paw.op(o, "", h) : {FAd.step.op(x, _) == (FAd.Running{Ad.Live.step(x, o)}, FAd.put_live(Ad.Live.step(x, o), "")) : FAd.St & String}
  {==}
