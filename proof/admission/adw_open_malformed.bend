# eukhe: the proof of LAW adw_open_malformed

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission.bend as Admission

def Admission.adw_open_malformed(s, h):
  %Equal.sym(Wr.Dec<+Sigma<Ad.Lim, x => Nat>>, FAd.get_open(s), Wr.Bad{}, h) : {FAd.open.go(_) == (FAd.Shut{}, Wr.err("admission: malformed open")) : FAd.St & String}
  {==}
