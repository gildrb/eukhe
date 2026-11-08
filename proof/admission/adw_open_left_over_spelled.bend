# eukhe: the proof of LAW adw_open_left_over_spelled
#
# PROOF: the spelled open is the entry's encoding (asp.lim), refused with
# input left over (adw_open_left_over).

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission.bend as Admission
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell
import ./base/spell.bend as LASpell
import ./adw_open_left_over.bend as PAdwOpenLeftOver

def Admission.adw_open_left_over_spelled(l, q, fits, c, t):
  %LASpell.asp.lim(l, Wr.put_nat(q, SCon{c, t})) : {FAd.open(_) == (FAd.Shut{}, Wr.err("admission: input left over")) : FAd.St & String}
  Admission.adw_open_left_over(l, q, c, t, fits)
