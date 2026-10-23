# eukhe: the proof of LAW adw_step_left_over

import Base
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.adw_step_left_over(x, o, c, rest, h):
  %LA.paw.op(o, SCon{c, rest}, h) : {FAd.step.op(x, _) == (FAd.Running{x}, Wr.err("admission: input left over")) : FAd.St & String}
  {==}
