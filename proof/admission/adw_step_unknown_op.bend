# eukhe: the proof of LAW adw_step_unknown_op
#
# PROOF: the op tag reads as itself or Bad (ws_nat_read), and a tag of 5
# or more is no op: Bad, the malformed error form, the controller kept.

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission.bend as Admission
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell
import ./base/spell.bend as LASpell

def auo.bad_op(b: Bool, +n: Nat, rest: String) -> {Wr.Bad{} == FAd.get_op.go(LAWireSpell.ws_nat_answer(b, 5n+n, rest)) : Wr.Dec<Ad.Op>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Admission.adw_step_unknown_op(x, n, rest):
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(5n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(5n+n), 5n+n, rest), LAWireSpell.ws_nat_read(5n+n, rest)) : {FAd.step.op(x, FAd.get_op.go(_)) == (FAd.Running{x}, Wr.err("admission: malformed op")) : FAd.St & String}
  %auo.bad_op(LawsBase.wire_fits(5n+n), n, rest) : {FAd.step.op(x, _) == (FAd.Running{x}, Wr.err("admission: malformed op")) : FAd.St & String}
  {==}
