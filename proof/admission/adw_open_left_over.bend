# eukhe: the proof of LAW adw_open_left_over

import Base
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.adw_open_left_over(l, q, c, rest, h):
  %LA.paw.open(l, q, SCon{c, rest}, h) : {FAd.open.go(_) == (FAd.Shut{}, Wr.err("admission: input left over")) : FAd.St & String}
  {==}
