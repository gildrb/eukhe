# eukhe: the proof of LAW adw_step_answers_spelled
#
# PROOF: the spelled op is the entry's encoding (asp.op), which answers
# the model's next controller (adw_step_answers), whose encoding is its
# spelling (asp.live).

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission.bend as Admission
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell
import ./base/spell.bend as LASpell
import ./adw_step_answers.bend as PAdwStepAnswers

def Admission.adw_step_answers_spelled(x, o, fits):
  %LASpell.asp.op(o, "") : {FAd.step(FAd.Running{x}, _) == (FAd.Running{Ad.Live.step(x, o)}, Admission.adw_spell_live(Ad.Live.step(x, o), "")) : FAd.St & String}
  %LASpell.asp.live(Ad.Live.step(x, o), "") : {FAd.step(FAd.Running{x}, FAd.put_op(o, "")) == (FAd.Running{Ad.Live.step(x, o)}, _) : FAd.St & String}
  Admission.adw_step_answers(x, o, fits)
