# eukhe: the proof of LAW adw_open_spelled
# The spec's spelling is the entry's encoding (LE.pae.lim), which opens
# the model's controller (adw_open_answers), spelled as the spec does.

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission.bend as Admission
import ./base/entry.bend as LE
import ./adw_open_answers.bend as POA

def Admission.adw_open_spelled(l, q, h):
  %LE.pae.lim(l, Wr.put_nat(q, "")) : {FAd.open(_) == (FAd.Running{Ad.Live{l, q, Nil{}, 0n}}, Admission.ads_spell_live(Ad.Live{l, q, Nil{}, 0n}, "")) : FAd.St & String}
  %Equal.sym(FAd.St & String, FAd.open(FAd.put_lim(l, Wr.put_nat(q, ""))), (FAd.Running{Ad.Live.new(l, q)}, FAd.put_live(Ad.Live.new(l, q), "")), Admission.adw_open_answers(l, q, h)) : {_ == (FAd.Running{Ad.Live{l, q, Nil{}, 0n}}, Admission.ads_spell_live(Ad.Live{l, q, Nil{}, 0n}, "")) : FAd.St & String}
  %LE.pae.live(Ad.Live{l, q, Nil{}, 0n}, "") : {(FAd.Running{Ad.Live{l, q, Nil{}, 0n}}, FAd.put_live(Ad.Live{l, q, Nil{}, 0n}, "")) == (FAd.Running{Ad.Live{l, q, Nil{}, 0n}}, _) : FAd.St & String}
  {==}
