# eukhe: the proof of LAW adw_open_answers

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.adw_open_answers(l, q, h):
  %LA.paw.open(l, q, "", h) : {FAd.open.go(_) == (FAd.Running{Ad.Live.new(l, q)}, FAd.put_live(Ad.Live.new(l, q), "")) : FAd.St & String}
  {==}
