# eukhe: the proof of LAW adw_step_answers_spelled
#
# PROOF: the spelled op is the entry's encoding (asp.op); the decoder
# reads that encoding back (paw.op), so the step answers the model's next
# controller (aws.step), whose encoding is its spelling (asp.live).

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission/wire.bend as AdmissionWire
import ../../laws/base.bend as LawsBase
import ./base/spell.bend as LASpell
import ./base/wire.bend as LAWire

def aws.step(+x: Ad.Live, +o: Ad.Op, h: {AdmissionWire.adw_op_fits(o) == True{} : Bool}) -> {FAd.step(FAd.Running{x}, FAd.put_op(o, "")) == (FAd.Running{Ad.Live.step(x, o)}, FAd.put_live(Ad.Live.step(x, o), "")) : FAd.St & String}:
  %LAWire.paw.op(o, "", h) : {FAd.step.op(x, _) == (FAd.Running{Ad.Live.step(x, o)}, FAd.put_live(Ad.Live.step(x, o), "")) : FAd.St & String}
  {==}

def AdmissionWire.adw_step_answers_spelled(x, o, fits):
  %LASpell.asp.op(o, "") : {FAd.step(FAd.Running{x}, _) == (FAd.Running{Ad.Live.step(x, o)}, AdmissionWire.adw_spell_live(Ad.Live.step(x, o), "")) : FAd.St & String}
  %LASpell.asp.live(Ad.Live.step(x, o), "") : {FAd.step(FAd.Running{x}, FAd.put_op(o, "")) == (FAd.Running{Ad.Live.step(x, o)}, _) : FAd.St & String}
  aws.step(x, o, fits)
