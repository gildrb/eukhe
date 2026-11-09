# eukhe: the proof of LAW adw_step_left_over_spelled
#
# PROOF: the spelled op is the entry's encoding (asp.op); the decoder
# reads it back with the rest left over (paw.op), refused with the
# controller kept (awk.step).

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission/wire.bend as AdmissionWire
import ../../laws/base.bend as LawsBase
import ./base/spell.bend as LASpell
import ./base/wire.bend as LAWire

def awk.step(+x: Ad.Live, +o: Ad.Op, +c: Char, +rest: String, h: {AdmissionWire.adw_op_fits(o) == True{} : Bool}) -> {FAd.step(FAd.Running{x}, FAd.put_op(o, SCon{c, rest})) == (FAd.Running{x}, Wr.err("admission: input left over")) : FAd.St & String}:
  %LAWire.paw.op(o, SCon{c, rest}, h) : {FAd.step.op(x, _) == (FAd.Running{x}, Wr.err("admission: input left over")) : FAd.St & String}
  {==}

def AdmissionWire.adw_step_left_over_spelled(x, o, fits, c, t):
  %LASpell.asp.op(o, SCon{c, t}) : {FAd.step(FAd.Running{x}, _) == (FAd.Running{x}, Wr.err("admission: input left over")) : FAd.St & String}
  awk.step(x, o, c, t, fits)
