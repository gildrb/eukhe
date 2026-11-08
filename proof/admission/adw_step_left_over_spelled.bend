# eukhe: the proof of LAW adw_step_left_over_spelled
#
# PROOF: the spelled op is the entry's encoding (asp.op), refused with
# input left over, the controller kept (adw_step_left_over).

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission.bend as Admission
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell
import ./base/spell.bend as LASpell
import ./adw_step_left_over.bend as PAdwStepLeftOver

def Admission.adw_step_left_over_spelled(x, o, fits, c, t):
  %LASpell.asp.op(o, SCon{c, t}) : {FAd.step(FAd.Running{x}, _) == (FAd.Running{x}, Wr.err("admission: input left over")) : FAd.St & String}
  Admission.adw_step_left_over(x, o, c, t, fits)
