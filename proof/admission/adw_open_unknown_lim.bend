# eukhe: the proof of LAW adw_open_unknown_lim
#
# PROOF: the limit tag reads as itself or Bad (ws_nat_read), and a tag of
# 2 or more is no limit: Bad, the malformed error form and the refused
# state.

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission.bend as Admission
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell
import ./base/spell.bend as LASpell
import ../../laws/admission/wire.bend as AdmissionWire

def aul.bad_lim(b: Bool, +n: Nat, rest: String) -> {Wr.Bad{} == FAd.get_lim.go(LAWireSpell.ws_nat_answer(b, 2n+n, rest)) : Wr.Dec<Ad.Lim>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def AdmissionWire.adw_open_unknown_lim(n, rest):
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest), LAWireSpell.ws_nat_read(2n+n, rest)) : {FAd.open.go(FAd.get_open.go(FAd.get_lim.go(_))) == (FAd.Shut{}, Wr.err("admission: malformed open")) : FAd.St & String}
  %aul.bad_lim(LawsBase.wire_fits(2n+n), n, rest) : {FAd.open.go(FAd.get_open.go(_)) == (FAd.Shut{}, Wr.err("admission: malformed open")) : FAd.St & String}
  {==}
