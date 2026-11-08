# eukhe: the proof of LAW adw_open_answers_spelled
#
# PROOF: the spelled open is the entry's encoding (asp.lim), which
# answers the model's new controller (adw_open_answers), whose encoding is
# its spelling (asp.live).

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission.bend as Admission
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell
import ./base/spell.bend as LASpell
import ./adw_open_answers.bend as PAdwOpenAnswers

def Admission.adw_open_answers_spelled(l, q, fits):
  %LASpell.asp.lim(l, Wr.put_nat(q, "")) : {FAd.open(_) == (FAd.Running{Ad.Live{l, q, Nil{}, 0n}}, Admission.adw_spell_live(Ad.Live{l, q, Nil{}, 0n}, "")) : FAd.St & String}
  %LASpell.asp.live(Ad.Live{l, q, Nil{}, 0n}, "") : {FAd.open(FAd.put_lim(l, Wr.put_nat(q, ""))) == (FAd.Running{Ad.Live{l, q, Nil{}, 0n}}, _) : FAd.St & String}
  Admission.adw_open_answers(l, q, fits)
