# eukhe: the proof of LAW adw_open_left_over_spelled
#
# PROOF: the spelled open is the entry's encoding (asp.lim); the decoder
# reads it back with the rest left over (paw.open), refused (awl.open).

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission/wire.bend as AdmissionWire
import ../../laws/base.bend as LawsBase
import ./base/spell.bend as LASpell
import ./base/wire.bend as LAWire

def awl.open(+l: Ad.Lim, +q: Nat, +c: Char, +rest: String, h: {Bool.and(AdmissionWire.adw_lim_fits(l), LawsBase.wire_fits(q)) == True{} : Bool}) -> {FAd.open(FAd.put_lim(l, Wr.put_nat(q, SCon{c, rest}))) == (FAd.Shut{}, Wr.err("admission: input left over")) : FAd.St & String}:
  %LAWire.paw.open(l, q, SCon{c, rest}, h) : {FAd.open.go(_) == (FAd.Shut{}, Wr.err("admission: input left over")) : FAd.St & String}
  {==}

def AdmissionWire.adw_open_left_over_spelled(l, q, fits, c, t):
  %LASpell.asp.lim(l, Wr.put_nat(q, SCon{c, t})) : {FAd.open(_) == (FAd.Shut{}, Wr.err("admission: input left over")) : FAd.St & String}
  awl.open(l, q, c, t, fits)
