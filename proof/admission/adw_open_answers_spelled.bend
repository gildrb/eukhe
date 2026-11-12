# eukhe: the proof of LAW adw_open_answers_spelled
#
# PROOF: the spelled open is the entry's encoding (asp.lim); the decoder
# reads that encoding back (paw.open), so the open answers the new
# controller (awa.open), whose encoding is its spelling (asp.live).

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission/wire.bend as AdmissionWire
import ../../laws/base.bend as LawsBase
import ./base/spell.bend as LASpell
import ./base/wire.bend as LAWire

def awa.open(+l: Ad.Lim, +q: Nat, h: {Bool.and(AdmissionWire.adw_lim_fits(l), LawsBase.wire_fits(q)) == True{} : Bool}) -> {FAd.open(FAd.put_lim(l, Wr.put_nat(q, ""))) == (FAd.Running{Ad.Live.new(l, q)}, FAd.put_live(Ad.Live.new(l, q), "")) : FAd.St & String}:
  %LAWire.paw.open(l, q, "", h) : {FAd.open.go(_) == (FAd.Running{Ad.Live.new(l, q)}, FAd.put_live(Ad.Live.new(l, q), "")) : FAd.St & String}
  {==}

def AdmissionWire.adw_open_answers_spelled(l, q, fits):
  %LASpell.asp.lim(l, Wr.put_nat(q, "")) : {FAd.open(_) == (FAd.Running{Ad.Live{l, q, Nil{}, 0n}}, AdmissionWire.adw_spell_live(Ad.Live{l, q, Nil{}, 0n}, "")) : FAd.St & String}
  %LASpell.asp.live(Ad.Live{l, q, Nil{}, 0n}, "") : {FAd.open(FAd.put_lim(l, Wr.put_nat(q, ""))) == (FAd.Running{Ad.Live{l, q, Nil{}, 0n}}, _) : FAd.St & String}
  awa.open(l, q, fits)
