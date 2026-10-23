# eukhe: the proof of LAW adw_step_malformed

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../LAWS.bend as Laws

def Laws.adw_step_malformed(x, s, h):
  %Equal.sym(Wr.Dec<Ad.Op>, FAd.get_op(s), Wr.Bad{}, h) : {FAd.step.op(x, _) == (FAd.Running{x}, Wr.err("admission: malformed op")) : FAd.St & String}
  {==}
